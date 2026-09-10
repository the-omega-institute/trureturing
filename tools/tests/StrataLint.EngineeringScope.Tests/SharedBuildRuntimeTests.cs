using StrataLint.TestSupport;
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
        Write(".gitignore", "build/\n.lake/\n**/bin/\n**/obj/\n");
        // The owning project's restore has already supplied these pinned packages.
        // This fixture exercises transport without a network package source.
        Write("NuGet.Config", "<configuration><packageSources><clear /></packageSources></configuration>\n");
        Write("global.json", File.ReadAllText(Path.Combine(repository, "global.json")));
        Write("tools/scripts/ci-build-outputs.targets", File.ReadAllText(Path.Combine(repository, "tools/scripts/ci-build-outputs.targets")));
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
        const string testProject = "tools/tests/Runtime/Runtime.csproj";
        Write(testProject, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <IsTestProject>true</IsTestProject><RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup>
            <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
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
        SharedBuildContractTests.Git(root, "add", ".");
        SharedBuildContractTests.Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "runtime fixture");
        using var output = new StringWriter();
        using var buildDeadline = new CancellationTokenSource(TestBudgets.WorkflowProcessHangGuard);
        // ci-stage.sh uses pwd -P; match that physical root on macOS's /var alias.
        var physicalRoot = SharedBuildContractTests.Git(root, "rev-parse", "--show-toplevel");
        Assert.True(new CommonStages(physicalRoot, output, buildDeadline.Token).Run("build", null) == 0, output.ToString());
        var build = CommonExecutionEvidence.ValidateBuild(root);
        Assert.Equal(new[] { "restore-StrataLint", "build" }, build.Steps.Select(step => step.Name));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
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
    }
}
