using StrataLint.TestSupport;
using System.Text.Json;
using System.Text.RegularExpressions;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class SharedBuildRuntimeTests
{
    [Fact]
    public void CompilerOwnedRuntimeMovesAndExecutesWithoutProducerOrPackagePaths()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var root = fixture.Root;
        var repository = TestRepositoryLayout.FindRoot();
        foreach (var path in new[] { CurrentExecutionContractTests.CandidateFixture.First, CurrentExecutionContractTests.CandidateFixture.Second })
            TemporaryFileSystem.File.Delete(Path.Combine(root, path));
        Write(".gitignore", "build/\n.lake/\n.judge-binaries/\n**/bin/\n**/obj/\n__pycache__/\n");
        // The owning project's restore has already supplied these pinned packages.
        // This fixture exercises transport without a network package source.
        Write("NuGet.Config", "<configuration><packageSources><clear /></packageSources></configuration>\n");
        Write("global.json", File.ReadAllText(Path.Combine(repository, "global.json")));
        Write("tools/scripts/ci-build-outputs.targets", File.ReadAllText(Path.Combine(repository, "tools/scripts/ci-build-outputs.targets")));
        foreach (var path in new[] { "tools/scripts/ci-stage.sh", "tools/scripts/report/dotnet_producer.py",
                     "tools/scripts/report/JudgeSeedTask.cs", "tools/scripts/report/JudgeSeedTask.csproj",
                     "tools/scripts/worktree/lean_actions.py", "tools/scripts/worktree/lean_cache.py",
                     "tools/scripts/worktree/lean_cache_release.py" })
            Write(path, File.ReadAllText(Path.Combine(repository, path)));
        Write("lean-toolchain", "leanprover/lean4:fixture\n");
        Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"}]}\n");
        // Exercise the canonical stage and real compiler. Only supervisor process
        // management and the location of the stage runner are fixture adapters.
        Write("tools/scripts/report/report-supervisor.sh", "while [[ $1 != -- ]]; do shift; done\nshift\nexec \"$@\"\n");
        var projects = new[] { ("StrataLint.Cli", "StrataLint"), ("StrataLint.EngineeringScope", "StrataLint.EngineeringScope"),
            ("StrataLint.Scribe.Documents", "StrataLint.Scribe.Documents") };
        foreach (var (project, assembly) in projects)
        {
            Write($"tools/{project}/{project}.csproj", $"""
                <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
                <AssemblyName>{assembly}</AssemblyName><GenerateRuntimeConfigurationFiles>true</GenerateRuntimeConfigurationFiles>
                <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup></Project>
                """);
            Write($"tools/{project}/Value.cs", $"namespace {project}; public class Value {{ public static void Require(int metaClear) {{ }} }}\n");
        }
        const string proofProject = "tools/tests/CompileFailProof/CompileFailProof.csproj";
        Write(proofProject, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup>
            <ItemGroup><ProjectReference Include="../../StrataLint.Cli/StrataLint.Cli.csproj" /></ItemGroup></Project>
            """);
        Write("tools/tests/CompileFailProof/MissingCapability.cs", "public class MissingCapability { public void Proof() => StrataLint.Cli.Value.Require(); }\n");
        const string bannedProject = "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj";
        Write(bannedProject, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile><WarningsAsErrors>RS0030</WarningsAsErrors></PropertyGroup>
            <ItemGroup><PackageReference Include="Microsoft.CodeAnalysis.BannedApiAnalyzers" Version="5.6.0" />
            <AdditionalFiles Include="BannedSymbols.txt" /></ItemGroup></Project>
            """);
        Write("tools/tests/BannedApiCompileFailProof/BannedSymbols.txt", "M:System.IO.File.ReadAllText(System.String); forbidden in fixture\n");
        Write("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs",
            "public class Banned { public string Read() => System.IO.File.ReadAllText(\"unused\"); } // banned-api-proof\n");
        var cliProject = "tools/StrataLint.Cli/StrataLint.Cli.csproj";
        Write(cliProject, File.ReadAllText(Path.Combine(root, cliProject)).Replace("</PropertyGroup>", "<OutputType>Exe</OutputType></PropertyGroup>", StringComparison.Ordinal));
        Write("tools/StrataLint.Cli/Program.cs", "System.Console.WriteLine(\"deterministic-selftest\");\n");
        const string testProject = "tools/tests/Runtime/Runtime.csproj";
        Write(testProject, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <IsTestProject>true</IsTestProject><RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup>
            <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
            <PackageReference Include="Microsoft.CodeAnalysis.BannedApiAnalyzers" Version="5.6.0" />
            <PackageReference Include="xunit" Version="2.9.3" /><PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" />
            <ProjectReference Include="../../StrataLint.Cli/StrataLint.Cli.csproj" />
            <ProjectReference Include="../../StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" />
            <ProjectReference Include="../../StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj" /></ItemGroup></Project>
            """);
        Write("tools/tests/Runtime/RuntimeTests.cs", """
            public class RuntimeTests {
                [Xunit.Fact] public void RuntimeRuns() {
                    Xunit.Assert.NotNull(new StrataLint.Cli.Value());
                    var packages = System.Environment.GetEnvironmentVariable("NUGET_PACKAGES");
                    Xunit.Assert.True(System.IO.File.Exists(System.IO.Path.Combine(packages, "xunit/2.9.3/xunit.nuspec")));
                    Xunit.Assert.True(System.IO.File.Exists(System.IO.Path.Combine(packages, "xunit/2.9.3/.nupkg.metadata")));
                }
            }
            """);
        Run("dotnet", "new", "sln", "--name", "StrataLint", "--format", "sln", "--output", "tools");
        Run("dotnet", "sln", "tools/StrataLint.sln", "add", testProject);
        Run("dotnet", "restore", "tools/StrataLint.sln", "--use-lock-file");
        Run("dotnet", "restore", proofProject, "--use-lock-file");
        Run("dotnet", "restore", bannedProject, "--use-lock-file");
        SharedBuildContractTests.Git(root, "add", ".");
        SharedBuildContractTests.Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "runtime fixture");
        using var output = new StringWriter();
        // ci-stage.sh uses pwd -P; match that physical root on macOS's /var alias.
        var physicalRoot = SharedBuildContractTests.Git(root, "rev-parse", "--show-toplevel");
        var dotnet = SharedBuildContractTests.Process(root, "which", ["dotnet"]).Text.Trim();
        var scope = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        Write("build/bin/dotnet", """
            #!/bin/bash
            set -euo pipefail
            echo "$*" >> build/dotnet-calls
            if [[ "$1" == *StrataLint.EngineeringScope.dll ]]; then shift; exec "$CONTRACT_SCOPE" "$@"; fi
            if [[ "$1" == build ]]; then exec "$CONTRACT_DOTNET" "$@" -v:diag; fi
            exec "$CONTRACT_DOTNET" "$@"
            """);
        File.SetUnixFileMode(Path.Combine(root, "build/bin/dotnet"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var environment = new Dictionary<string, string> {
            ["PATH"] = Path.Combine(physicalRoot, "build/bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
            ["CONTRACT_SCOPE"] = scope, ["CONTRACT_DOTNET"] = dotnet,
            ["DOTNET_CLI_UI_LANGUAGE"] = "en-US",
            ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "2", ["GITHUB_EVENT_NAME"] = "push",
            ["GITHUB_REF"] = "refs/heads/integration-ci-current-stability-0909-tests", ["STRATALINT_CACHE_WRITES"] = "true",
            ["STRATALINT_CHECK_SUCCEEDED"] = "false", ["STRATALINT_BUILD_SUCCEEDED"] = "true" };
        var cold = Stage("cold", "build");
        Assert.Equal(4, Compilers(cold));
        Assert.Single(Calls(), call => call == "sln tools/StrataLint.sln list");
        var build = CommonExecutionEvidence.ValidateBuild(root);
        Assert.Equal(new[] { "restore-StrataLint", "build" }, build.Steps.Select(step => step.Name));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
        Cache("snapshot");
        var manifest = Path.Combine(root, "build/lean-cache/judge/manifest.json");
        Assert.True(File.Exists(manifest));
        using var seed = JsonDocument.Parse(File.ReadAllText(manifest));
        var key = seed.RootElement.GetProperty("key").GetString()!;
        Assert.DoesNotContain(seed.RootElement.GetProperty("files").EnumerateArray(), item =>
            item.GetProperty("path").GetString()!.Contains("build/ci/", StringComparison.Ordinal));
        foreach (var project in projects.Select(item => "tools/" + item.Item1).Append("tools/tests/Runtime"))
            foreach (var kind in new[] { "bin", "obj" }) Directory.Delete(Path.Combine(root, project, kind), recursive: true);
        Directory.Delete(Path.Combine(root, "build/judge-seed"), recursive: true);
        Cache("restore", "--judge-key", key);
        var warm = Stage("warm", "build");
        Assert.Equal(0, Compilers(warm));
        Assert.Single(Calls(), call => call == "sln tools/StrataLint.sln list");
        Assert.Contains("\"status\": \"installed\"", warm, StringComparison.Ordinal);
        var fresh = CommonExecutionEvidence.ValidateBuild(root);
        Assert.NotEqual(build.Round, fresh.Round);
        build = fresh;
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
        environment["CI_BUILD_ROUND"] = build.Round;
        var engineering = Stage("engineering", "engineering");
        Assert.DoesNotContain(Calls(), call => call == "sln tools/StrataLint.sln list" || call.StartsWith("build tools/StrataLint.sln", StringComparison.Ordinal));
        Assert.Equal(2, Compilers(engineering)); // Both real negative proof compiles.
        Assert.Equal(1, Assert.Single(CommonExecutionEvidence.ValidateTests(root, [testProject]).Projects).Executed);
        Assert.Equal(build.Round, CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.EngineeringPath).Round);
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.CurrentPath)));
        var runtime = Assert.Single(CommonBuildOutputs.TestAssemblies(root, build));
        Assert.Equal(testProject, runtime.Key);
        Assert.Contains(build.Materials, material => material.Path.EndsWith("/testhost.dll", StringComparison.Ordinal));
        Assert.Contains(build.Materials, material => material.Path.EndsWith("/ref/StrataLint.dll", StringComparison.Ordinal));
        var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/runtime.tgz");
        Assert.Equal(0, Program.Run(["transport-pack", "--repository", root, "--stage", "build", "--commit", commit,
            "--run-id", "17", "--run-attempt", "2", "--archive", archive], TestResultEvidence.Load, output, output));
        var destination = TemporaryFileSystem.Directory.CreateTempSubdirectory("shared-build-consumer-").FullName;
        var offline = root + "-offline";
        try
        {
            SharedBuildContractTests.Git(root, "clone", "--quiet", "--no-hardlinks", root, destination);
            var extraction = SharedBuildContractTests.Process(destination, "python3", ["-c",
                "import pathlib,sys; sys.path.insert(0, sys.argv[1]); import ci; ci.extract(pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[3]))",
                Path.Combine(repository, "tools/scripts/workflow"), destination, archive]);
            Assert.True(extraction.Exit == 0, extraction.Text);
            Directory.Move(root, offline);
            var received = CommonExecutionEvidence.ValidateBuild(destination, build.Round);
            var assemblies = CommonBuildOutputs.TestAssemblies(destination, received);
            using var testOutput = new StringWriter();
            var consumerExit = Program.RunCurrentTests(destination, (project, results) =>
            {
                var execution = SharedBuildContractTests.Process(destination, "dotnet",
                    Program.BuildTestArguments(assemblies[project], results).ToArray(),
                    new Dictionary<string, string> { ["NUGET_PACKAGES"] = Path.Combine(destination, CommonBuildOutputs.PackagesPath) });
                testOutput.Write(execution.Text);
                return execution.Exit;
            }, testOutput, received);
            Assert.True(consumerExit == 0, testOutput.ToString());
            var tests = CommonExecutionEvidence.ValidateTests(destination, [testProject]);
            Assert.Equal(build.Round, tests.Round);
            Assert.Equal(1, Assert.Single(tests.Projects).Executed);
            Assert.Equal(build.Materials, CommonExecutionEvidence.ValidateBuild(destination).Materials);
            Assert.Empty(TemporaryFileSystem.Directory.EnumerateFiles(destination, "project.assets.json", SearchOption.AllDirectories));
            var restored = SharedBuildContractTests.Process(destination, "dotnet", ["restore", proofProject, "--locked-mode"]);
            Assert.True(restored.Exit == 0, restored.Text);
            var proof = SharedBuildContractTests.Process(destination, "dotnet",
                ["build", proofProject, "--no-restore", "--no-dependencies", "--configuration", "Release"]);
            Assert.True(CompilationProof.ValidateCapability(proof.Exit, proof.Text), proof.Text);
            Assert.Equal(build.Materials, CommonExecutionEvidence.ValidateBuild(destination).Materials);
        }
        finally
        {
            if (TemporaryFileSystem.Directory.Exists(offline)) Directory.Move(offline, root);
            TemporaryFileSystem.Directory.Delete(destination, recursive: true);
        }
        Cache("restore", "--judge-key", key);
        Write("tools/StrataLint.Cli/Program.cs", "not valid C#\n");
        Stage("wrong-candidate", "build", expected: 1);
        foreach (var path in new[] { CommonExecutionEvidence.BuildPath, CommonExecutionEvidence.EngineeringPath,
                     CommonExecutionEvidence.CurrentPath, CommonExecutionEvidence.TestsPath })
            Assert.False(File.Exists(Path.Combine(root, path)));

        void Write(string path, string text)
        {
            var full = Path.Combine(root, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            TemporaryFileSystem.File.WriteAllText(full, text);
        }
        void Run(string executable, params string[] arguments)
        {
            var result = SharedBuildContractTests.Process(root, executable, arguments);
            Assert.True(result.Exit == 0, result.Text);
        }
        string[] Calls() => File.ReadAllLines(Path.Combine(root, "build/dotnet-calls"));
        static int Compilers(string text) => Regex.Matches(text, "Task \\\"Csc\\\"(?: \\(TaskId:\\d+\\))?").Count;
        string Stage(string label, string stage, int expected = 0)
        {
            File.Delete(Path.Combine(root, "build/dotnet-calls"));
            var result = SharedBuildContractTests.Process(physicalRoot, "/bin/bash", ["tools/scripts/ci-stage.sh", stage], environment,
                TestBudgets.WorkflowProcessHangGuard);
            var evidence = Environment.GetEnvironmentVariable("JUDGE_SEED_EVIDENCE");
            if (evidence is not null)
            {
                Directory.CreateDirectory(evidence);
                File.WriteAllText(Path.Combine(evidence, "shared-" + label + ".log"), result.Text);
                foreach (var file in Directory.EnumerateFiles(Path.Combine(root, "build/ci"), "*", SearchOption.AllDirectories)
                             .Where(path => path.EndsWith(".json", StringComparison.Ordinal) || path.EndsWith(".trx", StringComparison.Ordinal)))
                {
                    var target = Path.Combine(evidence, label, Path.GetRelativePath(Path.Combine(root, "build/ci"), file));
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(file, target, overwrite: true);
                }
            }
            Assert.True(result.Exit == expected, result.Text);
            return result.Text;
        }
        void Cache(string command, params string[] arguments)
        {
            var result = SharedBuildContractTests.Process(physicalRoot, "python3",
                new[] { "tools/scripts/worktree/lean_actions.py", command, "--repository", physicalRoot, "--layers", "judge" }.Concat(arguments).ToArray(), environment);
            Assert.True(result.Exit == 0, result.Text);
        }
    }
}
