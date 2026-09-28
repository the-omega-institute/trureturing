using StrataLint.EngineeringScope;
using System.Diagnostics;
using System.Xml.Linq;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.StageIntegration.Tests;

[Collection("StrataLint.StageIntegration.Tests process boundary")]
public sealed class EngineeringScopeProgramTests
{
    [Theory]
    [InlineData(false, 0)]
    [InlineData(true, 0)]
    [InlineData(false, 73)]
    public void ColdSdkPreparationPrecedesRealConcurrentTests(bool failingTest, int preparationExit)
    {
        if (OperatingSystem.IsWindows()) return; // The observed startup boundary and forwarding fixture are Unix.
        using var fixture = new ExecutionFixture();
        var root = fixture.Root;
        fixture.Write("global.json", "{\"sdk\":{\"version\":\"10.0.103\",\"rollForward\":\"latestMinor\"}}");
        foreach (var project in new[] { ExecutionFixture.First, ExecutionFixture.Second })
        {
            var name = Path.GetFileNameWithoutExtension(project);
            fixture.Write(project, """
                <Project Sdk="Microsoft.NET.Sdk">
                  <PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject><NuGetAudit>false</NuGetAudit></PropertyGroup>
                  <ItemGroup>
                    <PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
                    <PackageReference Include="xunit" Version="2.9.3" />
                    <PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" />
                  </ItemGroup>
                </Project>
                """);
            fixture.Write(Path.GetDirectoryName(project) + "/Probe.cs", $$"""
                using System;
                using System.IO;
                using System.Threading;
                using Xunit;
                public sealed class {{name}}Probe {
                  [Fact] public void Runs() {
                    Assert.Null(Environment.GetEnvironmentVariable("CANDIDATE_SHA"));
                    var sync = Environment.GetEnvironmentVariable("PROBE_SYNC");
                    if (!string.IsNullOrEmpty(sync)) {
                      File.WriteAllText(Path.Combine(sync, "{{name}}.entered"), "entered");
                      if (!SpinWait.SpinUntil(() => File.Exists(Path.Combine(sync, "{{(name == "First" ? "Second" : "First")}}.entered")),
                          TimeSpan.FromTicks({{TestBudgets.WorkflowProcessHangGuard.Ticks}})))
                        throw new TimeoutException("infrastructure-hang-guard expired waiting for concurrent test");
                      File.WriteAllText(Path.Combine(sync, "{{name}}.overlapped"), "both entered");
                    }
                    Assert.True({{(!(failingTest && name == "Second")).ToString().ToLowerInvariant()}});
                  }
                }
                """);
            Run(root, "dotnet", ["build", project, "--configuration", "Release", "--nologo"]);
        }
        fixture.Track();
        SealProbeBuild(root, ExecutionFixture.First, ExecutionFixture.Second);
        var state = Path.Combine(root, "build/startup-observation");
        Directory.CreateDirectory(state);
        var environment = new Dictionary<string, string>(DotnetFixtureProfile.Create(Path.Combine(root, "build/cold")))
        {
            ["XDG_DATA_HOME"] = Path.Combine(root, "build/cold/xdg"),
            ["CANDIDATE_SHA"] = "ambient-candidate",
            ["PROBE_STATE"] = state,
            ["PROBE_SYNC"] = state,
            ["PROBE_PREPARATION_EXIT"] = preparationExit.ToString(System.Globalization.CultureInfo.InvariantCulture),
            ["PROBE_DOTNET"] = Path.Combine(Environment.GetEnvironmentVariable("DOTNET_ROOT")!, "dotnet"),
            ["PROBE_ROOT"] = root,
            ["PROBE_PACKAGES"] = Path.Combine(root, CommonBuildOutputs.PackagesPath),
            ["DOTNET_ADD_GLOBAL_TOOLS_TO_PATH"] = "false",
            ["DOTNET_SKIP_FIRST_TIME_EXPERIENCE"] = "0",
        };
        Assert.True(File.Exists(environment["PROBE_DOTNET"]));
        Directory.CreateDirectory(environment["PROBE_PACKAGES"]);
        var wrapper = Path.Combine(root, "build/observer/dotnet");
        fixture.Write("build/observer/dotnet", """
            #!/bin/sh
            set -u
            [ "$PWD" = "$PROBE_ROOT" ] && [ "$CI" = true ] && [ "$DOTNET_CLI_UI_LANGUAGE" = en-US ] &&
              [ "${CANDIDATE_SHA+x}" != x ] && [ "$NUGET_PACKAGES" = "$PROBE_PACKAGES" ] || exit 75
            if [ "$1" = test ] && [ "$2" = --help ]; then
              printf 'prepare\n' >> "$PROBE_STATE/order"
              printf 'initialization stdout: error and warning usage\n'
              printf 'warning: initialization stderr diagnostic\n' >&2
              if [ "$PROBE_PREPARATION_EXIT" != 0 ]; then
                printf 'intentional initialization failure\n' >&2
                exit "$PROBE_PREPARATION_EXIT"
              fi
              "$PROBE_DOTNET" "$@"
              code=$?
              [ "$code" = 0 ] || exit "$code"
              mkdir "$PROBE_STATE/first-use" "$PROBE_STATE/migration"
              cp -p "$DOTNET_CLI_HOME"/.dotnet/*.dotnetFirstUseSentinel "$PROBE_STATE/first-use/" || exit 76
              cp -p "$XDG_DATA_HOME"/NuGet/Migrations/* "$PROBE_STATE/migration/" || exit 77
              printf 'prepared\n' >> "$PROBE_STATE/order"
              exit 0
            fi
            printf 'child:%s\n' "$2" >> "$PROBE_STATE/order"
            "$PROBE_DOTNET" "$@"
            code=$?
            printf '%s:%s\n' "$code" "$2" >> "$PROBE_STATE/exits"
            exit "$code"
            """ + "\n");
        File.SetUnixFileMode(wrapper, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        environment["PATH"] = Path.GetDirectoryName(wrapper) + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH");
        Assert.Empty(Directory.GetFiles(environment["DOTNET_CLI_HOME"], "*.dotnetFirstUseSentinel", SearchOption.AllDirectories));
        Assert.False(Directory.Exists(environment["XDG_DATA_HOME"]));
        // An unsuccessful initialization must also invalidate a previous receipt.
        File.WriteAllText(Path.Combine(root, CommonExecutionEvidence.TestsPath), "stale receipt");
        var executable = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var result = EngineeringProcess.Capture(root, executable, ["--repository", root], environment,
            TestBudgets.LongWorkflowProcessHangGuard);
        Assert.True(result.Exit == (preparationExit != 0 ? preparationExit : failingTest ? 1 : 0), result.StandardOutput + result.StandardError);
        var order = File.ReadAllLines(Path.Combine(state, "order"));
        Assert.Equal("prepare", order[0]);
        Assert.Contains("warning: initialization stderr diagnostic", result.StandardError, StringComparison.Ordinal);
        if (preparationExit != 0)
        {
            Assert.Single(order);
            Assert.Contains("initialization stdout: error and warning usage", result.StandardOutput, StringComparison.Ordinal);
            Assert.Contains("intentional initialization failure", result.StandardError, StringComparison.Ordinal);
            Assert.Contains("raw_exit=73", result.StandardOutput, StringComparison.Ordinal);
            Assert.DoesNotContain("ENGINEERING_TEST_PROJECT ", result.StandardOutput, StringComparison.Ordinal);
            Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
            Assert.Empty(Directory.GetFiles(Path.Combine(root, CommonExecutionEvidence.RootPath), "*.trx", SearchOption.AllDirectories));
            return;
        }
        Assert.DoesNotContain("initialization stdout: error and warning usage", result.StandardOutput, StringComparison.Ordinal);
        Assert.DoesNotContain("--blame-crash", result.StandardOutput, StringComparison.Ordinal);
        Assert.Equal(4, order.Length);
        Assert.Equal("prepared", order[1]);
        Assert.All(order.Skip(2), line => Assert.StartsWith("child:", line, StringComparison.Ordinal));
        foreach (var (saved, current) in new[] {
            ("first-use", Path.Combine(environment["DOTNET_CLI_HOME"], ".dotnet")),
            ("migration", Path.Combine(environment["XDG_DATA_HOME"], "NuGet/Migrations")) })
        {
            var marker = Assert.Single(Directory.GetFiles(Path.Combine(state, saved)));
            var actual = Path.Combine(current, Path.GetFileName(marker));
            Assert.Equal(File.ReadAllBytes(marker), File.ReadAllBytes(actual));
            Assert.Equal(File.GetLastWriteTimeUtc(marker), File.GetLastWriteTimeUtc(actual));
        }
        var exits = File.ReadAllLines(Path.Combine(state, "exits"));
        Assert.Equal(2, exits.Length);
        var trxs = Directory.GetFiles(Path.Combine(root, CommonExecutionEvidence.RootPath), "*.trx", SearchOption.AllDirectories);
        Assert.Equal(2, trxs.Length);
        var identities = new HashSet<string>(StringComparer.Ordinal);
        foreach (var trx in trxs)
        {
            var document = XDocument.Load(trx);
            var test = Assert.Single(document.Descendants(), element => element.Name.LocalName == "UnitTestResult");
            var definition = Assert.Single(document.Descendants(), element => element.Name.LocalName == "UnitTest");
            var storage = Path.GetFileNameWithoutExtension((string)definition.Attribute("storage")!);
            var assembly = Assert.Single(new[] { "First", "Second" }, name => string.Equals(name, storage, StringComparison.OrdinalIgnoreCase));
            Assert.Equal(assembly + "Probe.Runs", (string?)test.Attribute("testName"));
            Assert.Equal((string?)definition.Attribute("id"), (string?)test.Attribute("testId"));
            Assert.True(Guid.TryParse((string?)test.Attribute("testId"), out _));
            Assert.True(identities.Add((string)test.Attribute("testId")!));
            Assert.Equal("1", (string?)Assert.Single(document.Descendants(), element => element.Name.LocalName == "Counters").Attribute("executed"));
            var failed = failingTest && assembly == "Second";
            Assert.Equal(failed ? "Failed" : "Passed", (string?)test.Attribute("outcome"));
            Assert.Contains(exits, line => line == $"{(failed ? 1 : 0)}:tools/tests/{assembly}/bin/Release/net10.0/{assembly}.dll");
            Assert.True(File.Exists(Path.Combine(state, assembly + ".overlapped")));
        }
        if (failingTest)
        {
            Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(root));
            return;
        }
        CommonExecutionEvidence.ValidateTests(root);
        var build = CommonExecutionEvidence.ValidateBuild(root);
        CheckEvidenceFixture.Seal(root, "engineering", build);
        CommonExecutionEvidence.SealEngineering(root, build, CommonExecutionEvidence.EngineeringSteps.Select(name =>
            new StageStep(name, name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", "build/ci/probe-build.log")).ToArray());
        Assert.True(CommonExecutionEvidence.ExportTestSeed(root, TextWriter.Null));
        foreach (var pair in DotnetFixtureProfile.Create(Path.Combine(root, "build/reuse-cold"))) environment[pair.Key] = pair.Value;
        environment["XDG_DATA_HOME"] = Path.Combine(root, "build/reuse-cold/xdg");
        environment["PROBE_PREPARATION_EXIT"] = "73";
        File.Delete(Path.Combine(state, "order"));
        var reused = EngineeringProcess.Capture(root, executable, ["--repository", root], environment, TestBudgets.WorkflowProcessHangGuard);
        Assert.True(reused.Exit == 0, reused.StandardOutput + reused.StandardError);
        Assert.False(File.Exists(Path.Combine(state, "order")));
        Assert.Empty(Directory.GetFiles(environment["DOTNET_CLI_HOME"], "*.dotnetFirstUseSentinel", SearchOption.AllDirectories));
        Assert.False(Directory.Exists(environment["XDG_DATA_HOME"]));
        Assert.All(CommonExecutionEvidence.ValidateTests(root).Projects, project => Assert.Equal("reused", project.Status));
    }

    [Theory]
    [InlineData(true, true, 0)]
    [InlineData(true, false, 1)]
    [InlineData(false, true, 2)]
    public void CurrentRunnerExecutesPrebuiltTestsAndNeverRetries(bool prebuild, bool passes, int expected)
    {
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory("engineering-process-").FullName;
        try
        {
            const string project = "tools/tests/Probe/Probe.csproj";
            var directory = Path.Combine(root, "tools/tests/Probe");
            TemporaryFileSystem.Directory.CreateDirectory(directory);
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, ".gitignore"), ".lake/\nbuild/\nbin/\nobj/\n");
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, project), """
                <Project Sdk="Microsoft.NET.Sdk">
                  <PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject></PropertyGroup>
                  <Import Project="Dependencies.props" />
                </Project>
                """);
            // Package declarations are an explicit build input of this native fixture.
            TemporaryFileSystem.File.WriteAllText(Path.Combine(directory, "Dependencies.props"), """
                <Project>
                  <ItemGroup>
                    <PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
                    <PackageReference Include="xunit" Version="2.9.3" />
                    <PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" />
                  </ItemGroup>
                </Project>
                """);
            TemporaryFileSystem.File.WriteAllText(Path.Combine(directory, "Probe.cs"),
                "using Xunit; public sealed class Probe { [Fact] public void Runs() { Assert.True(" + (passes ? "true" : "false")
                + "); Assert.Null(System.Environment.GetEnvironmentVariable(\"CANDIDATE_SHA\")); } }");
            var retiredSuite = Path.Combine(root, "tools/tests/StrataLint.ScriptTests");
            TemporaryFileSystem.Directory.CreateDirectory(retiredSuite);
            TemporaryFileSystem.File.WriteAllText(Path.Combine(retiredSuite, "StrataLint.ScriptTests.csproj"),
                "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>");
            TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(root, "Meta"));
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, EngineeringRegistrationFixture.Path),
                EngineeringRegistrationFixture.Manifest(
                    new EngineeringProjectFixture("tools/tests/Probe/Probe.csproj", "Probe", "cross-cutting-test", true, ["tools/tests/Probe/**/*.cs"], BuildInputs: ["tools/tests/Probe/Dependencies.props"]),
                    new EngineeringProjectFixture("tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj", "StrataLint.ScriptTests", "cross-cutting-test", false, [])));
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, "global.json"), "{\"sdk\":{\"version\":\"10.0.103\"}}");
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, "Meta/ci-checks.json"), CommonCheckRegistrationFixture.Manifest(project));
            var registrationPath = Path.Combine(root, EngineeringRegistrationFixture.Path);
            foreach (var proof in new[] { "CompileFailProof", "BannedApiCompileFailProof" })
            {
                var proofProject = $"tools/tests/{proof}/{proof}.csproj";
                Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(root, proofProject))!);
                File.WriteAllText(Path.Combine(root, proofProject), "<Project />");
                File.WriteAllText(registrationPath, EngineeringRegistrationFixture.Append(File.ReadAllText(registrationPath),
                    new EngineeringProjectFixture(proofProject, proof, "compile-fail-proof", false, [$"tools/tests/{proof}/**/*.cs"])));
            }
            File.WriteAllText(Path.Combine(root, "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"), "// banned-api-proof\n");
            Run(root, "git", ["init", "-q"]);
            Run(root, "git", ["add", "."]);
            Run(root, "git", ["-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless"]);
            if (prebuild)
            {
                Run(root, "dotnet", ["build", project, "--configuration", "Release", "--nologo"]);
                SealProbeBuild(root, project);
            }
            using var output = new StringWriter();
            using var error = new StringWriter();
            // Capture the CLI boundary: its native test child inherits OS streams,
            // so in-process StringWriters cannot contain the intentional rejection.
            var environment = new Dictionary<string, string>(DotnetFixtureProfile.Create(root))
            {
                ["CANDIDATE_SHA"] = "ambient-candidate",
            };
            var executable = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
            var result = EngineeringProcess.Capture(root, executable, ["--repository", root], environment);
            output.Write(result.StandardOutput);
            error.Write(result.StandardError);
            Assert.True(result.Exit == expected, output + "\n" + error);
            if (!prebuild)
            {
                Assert.Empty(output.ToString());
                Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
                return;
            }
            Assert.Single(output.ToString().Split('\n'), line => line.StartsWith("ENGINEERING_TEST_PROJECT ", StringComparison.Ordinal));
            Assert.DoesNotContain("ENGINEERING_TEST_RETRY", output.ToString(), StringComparison.Ordinal);
            Assert.True(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
            var trx = Assert.Single(Directory.GetFiles(Path.Combine(root, CommonExecutionEvidence.RootPath), "*.trx", SearchOption.AllDirectories));
            var test = Assert.Single(XDocument.Load(trx).Descendants(), element => element.Name.LocalName == "UnitTestResult");
            Assert.Equal("Probe.Runs", (string?)test.Attribute("testName"));
            Assert.Equal(passes ? "Passed" : "Failed", (string?)test.Attribute("outcome"));
            if (!passes)
            {
                var message = Assert.Single(test.Descendants(), element => element.Name.LocalName == "Message");
                Assert.Contains("Assert.True() Failure", message.Value, StringComparison.Ordinal);
                Assert.Contains("Failed Probe.Runs", output.ToString(), StringComparison.Ordinal);
            }
            if (expected == 0)
            {
                var original = CommonExecutionEvidence.ValidateTests(root);
                var steps = CommonExecutionEvidence.EngineeringSteps.Select(name => new StageStep(name,
                    name.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", "build/ci/probe-build.log")).ToArray();
                var build = CommonExecutionEvidence.ValidateBuild(root);
                CheckEvidenceFixture.Seal(root, "engineering", build);
                CommonExecutionEvidence.SealEngineering(root, build, steps);
                Assert.True(CommonExecutionEvidence.ExportTestSeed(root, output));
                TemporaryFileSystem.File.AppendAllText(Path.Combine(root, ".gitignore"), "# unrelated doc-only candidate change\n");
                SealProbeBuild(root, project);
                output.GetStringBuilder().Clear();
                Assert.Equal(0, Program.Run(["--repository", root], TestResultEvidence.Load, output, error));
                Assert.DoesNotContain("ENGINEERING_TEST_PROJECT ", output.ToString(), StringComparison.Ordinal);
                var reused = CommonExecutionEvidence.ValidateTests(root);
                var row = Assert.Single(reused.Projects);
                Assert.Equal("reused", row.Status);
                Assert.Equal(original.Projects[0] with { Status = "reused" }, row);
                Assert.Equal(original.Materials, reused.Materials);
            }
        }
        finally
        {
            if (Environment.GetEnvironmentVariable("CI_TEST_REUSE_EVIDENCE") is { Length: > 0 } retention && prebuild)
            {
                var ci = Path.Combine(root, CommonExecutionEvidence.RootPath);
                foreach (var file in TemporaryFileSystem.Directory.EnumerateFiles(ci, "*", SearchOption.AllDirectories))
                {
                    var target = Path.Combine(retention, passes ? "passed" : "failed", Path.GetRelativePath(ci, file));
                    TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    TemporaryFileSystem.File.WriteAllBytes(target, TemporaryFileSystem.File.ReadAllBytes(file));
                }
            }
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void DeclaredExecutionEnvironmentChangesOnlyRegisteredProjectsAndMissingValueFails()
    {
        using var fixture = new ExecutionFixture();
        const string name = "CONTRACT_REGISTERED_TEST_ENVIRONMENT";
        var original = Environment.GetEnvironmentVariable(name);
        try
        {
            var manifestPath = Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path);
            var manifest = System.Text.Json.Nodes.JsonNode.Parse(TemporaryFileSystem.File.ReadAllText(manifestPath))!;
            manifest["projects"]![0]!["execution_environment"] = new System.Text.Json.Nodes.JsonArray(name);
            TemporaryFileSystem.File.WriteAllText(manifestPath, manifest.ToJsonString());
            Environment.SetEnvironmentVariable(name, "macos-arm64-sdk103-runtime10");
            fixture.Build();
            Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, directory) => { fixture.WriteTrx(directory, "Passed"); return 0; }, TextWriter.Null));
            var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
            CheckEvidenceFixture.Seal(fixture.Root, "engineering", build);
            CommonExecutionEvidence.SealEngineering(fixture.Root, build, CommonExecutionEvidence.EngineeringSteps.Select(step =>
                new StageStep(step, step.EndsWith("proof", StringComparison.Ordinal) ? 1 : 0, 0, "executed", "build/ci/fixture-build.log")).ToArray());
            Assert.True(CommonExecutionEvidence.ExportTestSeed(fixture.Root, TextWriter.Null));
            Environment.SetEnvironmentVariable(name, "linux-arm64-sdk103-runtime10");
            var selected = new List<string>();
            Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (project, directory) =>
            {
                selected.Add(project);
                fixture.WriteTrx(directory, "Passed");
                return 0;
            }, TextWriter.Null));
            Assert.Equal([ExecutionFixture.First], selected);
            Environment.SetEnvironmentVariable(name, null);
            var calls = 0;
            Assert.Throws<InvalidDataException>(() => Program.RunCurrentTests(fixture.Root, (_, _) => { ++calls; return 0; }, TextWriter.Null));
            Assert.Equal(0, calls);
        }
        finally { Environment.SetEnvironmentVariable(name, original); }
    }

    private static void SealProbeBuild(string root, params string[] projects)
    {
        var tests = projects.Select(project => new BuiltTestProject(project,
            Path.GetDirectoryName(project)!.Replace('\\', '/') + "/bin/Release/net10.0/" + Path.GetFileNameWithoutExtension(project) + ".dll")).ToArray();
        const string log = "build/ci/probe-build.log";
        CommonExecutionEvidence.Write(root, CommonBuildOutputs.TestsPath, tests);
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root, log), "native probe build\n");
        CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), tests.Select(test => test.Assembly).Concat([log, CommonBuildOutputs.TestsPath]),
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
    }

    private static void Run(string root, string command, string[] arguments)
    {
        var start = new ProcessStartInfo(command) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        if (command == "dotnet")
        {
            foreach (var pair in DotnetFixtureProfile.Create(root)) start.Environment[pair.Key] = pair.Value;
            start.Environment["XDG_DATA_HOME"] = Path.Combine(root, "build/restore-xdg");
            start.Environment["DOTNET_ADD_GLOBAL_TOOLS_TO_PATH"] = "false";
        }
        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult());
    }
}
