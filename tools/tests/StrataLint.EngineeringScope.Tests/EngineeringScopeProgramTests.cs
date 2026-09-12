using System.Diagnostics;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class EngineeringScopeProgramTests
{
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
                + "); Assert.Null(Environment.GetEnvironmentVariable(\"CI_WORKFLOW_CANDIDATE_SHA\")); } }");
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
            var ambientCandidate = Environment.GetEnvironmentVariable("CI_WORKFLOW_CANDIDATE_SHA");
            Environment.SetEnvironmentVariable("CI_WORKFLOW_CANDIDATE_SHA", "ambient-workflow-candidate");
            int exit;
            try
            {
                exit = Program.Run(["--repository", root], TestResultEvidence.Load, output, error);
            }
            finally
            {
                Environment.SetEnvironmentVariable("CI_WORKFLOW_CANDIDATE_SHA", ambientCandidate);
            }
            Assert.True(exit == expected, output + "\n" + error);
            if (!prebuild)
            {
                Assert.Empty(output.ToString());
                Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
                return;
            }
            Assert.Single(output.ToString().Split('\n'), line => line.StartsWith("ENGINEERING_TEST_PROJECT ", StringComparison.Ordinal));
            Assert.DoesNotContain("ENGINEERING_TEST_RETRY", output.ToString(), StringComparison.Ordinal);
            Assert.True(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
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
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
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
            Assert.Equal([CurrentExecutionContractTests.CandidateFixture.First], selected);
            Environment.SetEnvironmentVariable(name, null);
            var calls = 0;
            Assert.Throws<InvalidDataException>(() => Program.RunCurrentTests(fixture.Root, (_, _) => { ++calls; return 0; }, TextWriter.Null));
            Assert.Equal(0, calls);
        }
        finally { Environment.SetEnvironmentVariable(name, original); }
    }

    [Fact]
    public void CandidateTestInvocationIsPrebuiltWithMinimalVerbosity()
    {
        var arguments = Program.BuildTestArguments("tools/tests/Probe/Probe.csproj", "/tmp/results");
        Assert.Contains("--no-build", arguments);
        Assert.Contains("--no-restore", arguments);
        Assert.Equal("minimal", arguments[Array.IndexOf(arguments.ToArray(), "--verbosity") + 1]);
    }

    [Theory]
    [InlineData("--all")]
    [InlineData("--base")]
    [InlineData("--head")]
    [InlineData("--full")]
    public void RunnerRejectsFullAndHistoricalSelectionOptions(string option)
    {
        using var output = new StringWriter();
        using var error = new StringWriter();
        var exit = Program.Run(["--repository", "/missing-repository", option, "value"],
            TestResultEvidence.Load, output, error);
        Assert.Equal(2, exit);
        Assert.Contains("options must be", error.ToString(), StringComparison.Ordinal);
        Assert.Empty(output.ToString());
    }

    private static void SealProbeBuild(string root, string project)
    {
        const string assembly = "tools/tests/Probe/bin/Release/net10.0/Probe.dll";
        const string log = "build/ci/probe-build.log";
        CommonExecutionEvidence.Write(root, CommonBuildOutputs.TestsPath, new[] { new BuiltTestProject(project, assembly) });
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root, log), "native probe build\n");
        CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), [assembly, log, CommonBuildOutputs.TestsPath],
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray());
    }

    private static void Run(string root, string command, string[] arguments)
    {
        var start = new ProcessStartInfo(command) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult());
    }
}

[CollectionDefinition("Engineering scope process boundary", DisableParallelization = true)]
public sealed class EngineeringScopeProcessBoundaryCollection;
