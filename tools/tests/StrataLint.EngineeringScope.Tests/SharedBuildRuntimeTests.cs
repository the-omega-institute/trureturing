using StrataLint.TestSupport;
using System.Text.Json;
using System.Text.RegularExpressions;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
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
        // Match the repository's SDK policy: commit identity is not compiler input.
        Write("Directory.Build.props", "<Project><PropertyGroup><EnableSourceControlManagerQueries>false</EnableSourceControlManagerQueries></PropertyGroup></Project>\n");
        Write("tools/scripts/ci-build-outputs.targets", File.ReadAllText(Path.Combine(repository, "tools/scripts/ci-build-outputs.targets")));
        Write(PackageMaterialRegistry.RelativePath, JsonSerializer.Serialize(new {
            schemaVersion = 1, packageRootSource = "build-output:NuGetPackageRoot",
            packages = new[] { "microsoft.codeanalysis.bannedapianalyzers/5.6.0", "microsoft.codecoverage/18.0.1",
                "microsoft.net.test.sdk/18.0.1", "microsoft.testplatform.objectmodel/18.0.1", "microsoft.testplatform.testhost/18.0.1",
                "newtonsoft.json/13.0.3", "xunit/2.9.3", "xunit.abstractions/2.0.3", "xunit.analyzers/1.18.0",
                "xunit.assert/2.9.3", "xunit.core/2.9.3", "xunit.extensibility.core/2.9.3", "xunit.extensibility.execution/2.9.3",
                "xunit.runner.visualstudio/3.1.4" }.Order(StringComparer.Ordinal).Select(package => new {
                    packagePath = package, include = new[] { "**/*" }, exclude = new[] { "**/*.nupkg", "**/*.snupkg" } }) }));
        foreach (var path in new[] { "tools/scripts/ci-stage.sh", "tools/scripts/lib/resource-observation-lib.sh",
                     "tools/scripts/report/dotnet_producer.py",
                     "tools/scripts/workflow/ci.py", "tools/scripts/workflow/ci_plan.py",
                     "tools/scripts/report/JudgeSeedTask.cs", "tools/scripts/report/JudgeSeedTask.csproj",
                     "tools/scripts/report/JudgeSeed.targets",
                     "tools/scripts/worktree/lean_actions.py", "tools/scripts/worktree/lean_cache.py",
                     "tools/scripts/worktree/lean_cache_release.py", "tools/scripts/worktree/cache_material.py" })
            Write(path, File.ReadAllText(Path.Combine(repository, path)));
        var seedRegistration = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(Path.Combine(repository, "Meta/judge-seed.json")))!;
        seedRegistration["repository_files"] = new System.Text.Json.Nodes.JsonArray();
        Write("Meta/judge-seed.json", seedRegistration.ToJsonString());
        Write("lean-toolchain", "leanprover/lean4:fixture\n");
        Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"}]}\n");
        // Exercise the canonical stage and real compiler. Only supervisor process
        // management and the location of the stage runner are fixture adapters.
        Write("tools/scripts/report/report-supervisor.sh", "while [[ $1 != -- ]]; do shift; done\nshift\nexec \"$@\"\n");
        var projects = new[] { ("StrataLint.Cli", "StrataLint"), ("StrataLint.EngineeringScope", "StrataLint.EngineeringScope"),
            ("StrataLint.Scribe.Documents", "StrataLint.Scribe.Documents"), ("StrataLint.Lean", "StrataLint.Lean") };
        foreach (var (project, assembly) in projects)
        {
            Write($"tools/{project}/{project}.csproj", $"""
                <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
                <AssemblyName>{assembly}</AssemblyName><OutputType>{(project == "StrataLint.Lean" ? "Exe" : "Library")}</OutputType><GenerateRuntimeConfigurationFiles>true</GenerateRuntimeConfigurationFiles>
                <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup></Project>
                """);
            Write($"tools/{project}/Value.cs", $"namespace {project}; public class Value {{ public static void Require(int metaClear) {{ }} }}\n");
        }
        Write("tools/StrataLint.Lean/Program.cs", "internal static class Program { public static void Main() => System.Console.WriteLine(\"report utility runtime\"); }\n");
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
        Write("tools/StrataLint.Cli/Program.cs", "System.Console.WriteLine(\"SELFTEST PASS\");\n");
        Write("Meta/ci-checks.json", CommonCheckRegistrationFixture.Manifest(cliProject));
        Write("Meta/ci-resources.json", JsonSerializer.Serialize(new { schema = "ci-resource-execution-v1",
            resources = new[] { new { id = "build", projects = new[] { cliProject }, checks = Array.Empty<string>(), steps = Array.Empty<string>() } } }));
        Write("Meta/FILEMAP.toml", """
            schema_version = 4
            resources = [{ id = "build", stage = "build", owner = "tools/scripts/workflow/ci.py", prerequisites = [], tools = [], cache_layers = [], cache_activation = {}, materials = ["Meta/ci-checks.json", "Meta/ci-resources.json", "Meta/engineering-projects.json"] }]
            [residence_policy]
            case_id = "FIXTURE"
            desired = "registered"
            known_violation_count = 0
            status = "closed"
            [[files]]
            pattern = "**"
            require = ["build"]
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["test"]
            verified_by = ["test"]
            artifact_id = "none"
            runtime_disposition = "committed-source"
            """ + "\n");
        const string testProject = "tools/tests/Runtime/Runtime.csproj";
        Write(testProject, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <IsTestProject>true</IsTestProject><RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup>
            <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
            <PackageReference Include="Microsoft.CodeAnalysis.BannedApiAnalyzers" Version="5.6.0" />
            <PackageReference Include="xunit" Version="2.9.3" /><PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" />
            <ProjectReference Include="../../StrataLint.Cli/StrataLint.Cli.csproj" />
            <ProjectReference Include="../../StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" />
            <ProjectReference Include="../../StrataLint.Lean/StrataLint.Lean.csproj" />
            <ProjectReference Include="../../StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj" />
            <ProjectReference Include="../../scripts/report/JudgeSeedTask.csproj" /></ItemGroup></Project>
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
        const string excludedProject = "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
        Write(excludedProject, """
            <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
            <IsTestProject>true</IsTestProject><RestorePackagesWithLockFile>true</RestorePackagesWithLockFile></PropertyGroup>
            <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
            <PackageReference Include="xunit" Version="2.9.3" /><PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" /></ItemGroup></Project>
            """);
        Write("tools/tests/StrataLint.ScriptTests/Unselected.cs", "namespace Fixture; public class Unselected { [Xunit.Fact] public void Runs() => Xunit.Assert.Equal(\"Fixture\", typeof(Unselected).Namespace); }\n");
        Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
            projects.Select(item => new EngineeringProjectFixture($"tools/{item.Item1}/{item.Item1}.csproj",
                item.Item2, "production", false, [$"tools/{item.Item1}/**/*.cs"], OwnedTestAssembly: "Runtime"))
            .Concat(new[] {
                new EngineeringProjectFixture(testProject, "Runtime", "cross-cutting-test", true, ["tools/tests/Runtime/**/*.cs"],
                    References: projects.Select(item => $"tools/{item.Item1}/{item.Item1}.csproj").Append("tools/scripts/report/JudgeSeedTask.csproj").ToArray()),
                new EngineeringProjectFixture(proofProject, "CompileFailProof", "compile-fail-proof", false,
                    ["tools/tests/CompileFailProof/**/*.cs"], References: [cliProject]),
                new EngineeringProjectFixture(bannedProject, "BannedApiCompileFailProof", "compile-fail-proof", false,
                    ["tools/tests/BannedApiCompileFailProof/**/*.cs"]),
                new EngineeringProjectFixture("tools/scripts/report/JudgeSeedTask.csproj", "JudgeSeedTask", "production", false,
                    ["tools/scripts/report/JudgeSeedTask.cs"], OwnedTestAssembly: "JudgeSeedTask.Tests"),
                new EngineeringProjectFixture(excludedProject, "StrataLint.ScriptTests", "cross-cutting-test", false,
                    ["tools/tests/StrataLint.ScriptTests/**/*.cs"]),
            }).ToArray()));
        Run("dotnet", "restore", testProject, "--use-lock-file", "-nr:false");
        Run("dotnet", "restore", proofProject, "--use-lock-file", "-nr:false");
        Run("dotnet", "restore", bannedProject, "--use-lock-file", "-nr:false");
        Run("dotnet", "restore", excludedProject, "--use-lock-file", "-nr:false");
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
            if [[ "$1" == build ]]; then exec "$CONTRACT_DOTNET" "$@" -v:minimal -clp:PerformanceSummary; fi
            exec "$CONTRACT_DOTNET" "$@"
            """);
        File.SetUnixFileMode(Path.Combine(root, "build/bin/dotnet"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var environment = new Dictionary<string, string> {
            ["PATH"] = Path.Combine(physicalRoot, "build/bin") + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
            ["CONTRACT_SCOPE"] = scope, ["CONTRACT_DOTNET"] = dotnet,
            ["DOTNET_CLI_UI_LANGUAGE"] = "en-US",
            ["CI_CSC_LOGGER_ASSEMBLY"] = Path.Combine(root, "missing-previous-observer.dll"),
            ["CI_PLAN_PATH"] = "", ["CI_CHANGES_PATH"] = "",
            ["CI_WORKFLOW_INPUTS"] = "null", ["CI_NEEDS"] = "{}", ["CI_BUILD_ROUND"] = "", ["CANDIDATE_SHA"] = "",
            ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "2", ["GITHUB_EVENT_NAME"] = "",
            ["GITHUB_EVENT_PATH"] = "", ["CI_PUSH_BEFORE"] = "", ["CI_PUSH_AFTER"] = "",
            ["GITHUB_REF"] = "refs/heads/integration-ci-current-stability-0909-tests", ["STRATALINT_CACHE_WRITES"] = "true",
            // This fixture exercises stage exports, independently of the outer workflow's deferred upload.
            ["CI_SEED_EXPORT"] = "automatic",
            ["STRATALINT_CHECK_SUCCEEDED"] = "false", ["STRATALINT_BUILD_SUCCEEDED"] = "true" };
        var cold = Stage("cold", "build");
        Assert.Equal(projects.Length + 2, Compilers(cold)); // Four utilities, Runtime, and the registered JudgeSeedTask.
        Assert.Equal(projects.Length + 2, ObservedCompilers(cold));
        var build = CommonExecutionEvidence.ValidateBuild(root);
        Assert.Equal(new[] { "restore-StrataLint", "build" }, build.Steps.Select(step => step.Name));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
        Assert.False(File.Exists(Path.Combine(root, "build/judge-seed/receipts", excludedProject + ".seed.json")));
        Cache("snapshot");
        var manifest = Path.Combine(root, "build/lean-cache/judge/manifest.json");
        Assert.True(File.Exists(manifest));
        using var seed = JsonDocument.Parse(File.ReadAllText(manifest));
        var key = seed.RootElement.GetProperty("key").GetString()!;
        Assert.DoesNotContain(seed.RootElement.GetProperty("files").EnumerateArray(), item =>
            item.GetProperty("path").GetString()!.Contains("build/ci/", StringComparison.Ordinal));
        foreach (var project in projects.Select(item => "tools/" + item.Item1).Append("tools/tests/Runtime").Append("tools/scripts/report"))
            foreach (var kind in new[] { "bin", "obj" }) Directory.Delete(Path.Combine(root, project, kind), recursive: true);
        Directory.Delete(Path.Combine(root, "build/judge-seed"), recursive: true);
        Cache("restore", "--judge-key", key);
        var warm = Stage("warm", "build");
        Assert.Equal(0, Compilers(warm));
        Assert.Equal(0, ObservedCompilers(warm));
        Assert.Contains("\"status\": \"installed\"", warm, StringComparison.Ordinal);
        // A narrow push must preserve the explicitly declared donor projects for
        // the next full build, without turning those projects into build roots.
        foreach (var scenario in new[] { "unchanged", "changed-unselected", "damaged-donor" })
        {
            var changedUnselected = scenario == "changed-unselected";
            NarrowPlan();
            ResetCompiledOutputs();
            Cache("restore", "--judge-key", key);
            var narrow = Stage(changedUnselected ? "narrow-before-change" : "narrow", "build");
            Assert.Equal(0, Compilers(narrow));
            Assert.Equal(new[] { cliProject }, CommonExecutionEvidence.ValidateBuild(root).Projects);
            if (scenario == "damaged-donor") Write("build/lean-cache/judge/manifest.json", "broken optional donor");
            Cache("snapshot");
            environment["CI_PLAN_PATH"] = "";
            environment["CI_CHANGES_PATH"] = "";
            if (changedUnselected)
            {
                Write("tools/tests/Runtime/RuntimeTests.cs", File.ReadAllText(Path.Combine(root, "tools/tests/Runtime/RuntimeTests.cs")) + "\n// changed while absent from the narrow build\n");
                SharedBuildContractTests.Git(root, "add", ".");
                SharedBuildContractTests.Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "change an unselected compiler input");
            }
            ResetCompiledOutputs();
            Cache("restore", "--judge-key", key);
            var restoredFull = Stage(scenario == "damaged-donor" ? "recovered-donor" : changedUnselected ? "retained-source-change" : "retained-full", "build");
            var expectedCompilers = scenario == "damaged-donor" ? projects.Length + 1 : changedUnselected ? 1 : 0;
            Assert.Equal(expectedCompilers, Compilers(restoredFull));
            Assert.Equal(expectedCompilers, ObservedCompilers(restoredFull));
            if (scenario == "damaged-donor")
                Assert.DoesNotContain(restoredFull.Split('\n').Where(line => line.StartsWith("JUDGE_CSC ", StringComparison.Ordinal))
                    .Select(line => JsonDocument.Parse(line["JUDGE_CSC ".Length..]).RootElement),
                    row => row.GetProperty("status").GetString() == "task-started"
                        && row.GetProperty("project").GetString() == Path.Combine(physicalRoot, cliProject));
            Cache("snapshot");
        }
        var fresh = CommonExecutionEvidence.ValidateBuild(root);
        Assert.NotEqual(build.Round, fresh.Round);
        build = fresh;
        Cache("snapshot"); // Warm Build also seals the obj bytes refreshed by normal MSBuild.
        Assert.True(File.Exists(manifest));
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.EngineeringPath)));
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
        environment["CI_BUILD_ROUND"] = build.Round;
        var engineering = Stage("engineering", "engineering");
        Assert.DoesNotContain(Calls(), call => call.StartsWith("build tools/StrataLint.sln", StringComparison.Ordinal));
        Assert.Equal(2, Compilers(engineering)); // Both real negative proof compiles.
        Assert.Equal(1, Assert.Single(CommonExecutionEvidence.ValidateTests(root, [testProject]).Projects).Executed);
        Assert.Equal(build.Round, CommonExecutionEvidence.Read<CommonStageRecord>(root, CommonExecutionEvidence.EngineeringPath).Round);
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.CurrentPath)));
        var originalChecks = CommonExecutionEvidence.ValidateChecks(root, "engineering", build);
        var reusedEngineering = Stage("engineering-warm", "engineering");
        var reusedEngineeringCompilers = Compilers(reusedEngineering);
        Assert.True(reusedEngineeringCompilers == 0,
            $"Warm engineering expected 0 Csc calls, actual {reusedEngineeringCompilers}.\n{reusedEngineering}");
        Assert.DoesNotContain(Calls(), call => call.Contains(" selftest", StringComparison.Ordinal)
            || call.StartsWith("restore tools/tests/CompileFailProof", StringComparison.Ordinal)
            || call.StartsWith("restore tools/tests/BannedApiCompileFailProof", StringComparison.Ordinal));
        Assert.All(CommonExecutionEvidence.ValidateChecks(root, "engineering", build).Units, unit =>
        {
            Assert.Equal("reused", unit.Status);
            Assert.Equal(originalChecks.Units.Single(original => original.Id == unit.Id).Operations, unit.Operations);
        });
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
                "import pathlib,sys; sys.path.insert(0, sys.argv[1]); import ci; ci.extract(pathlib.Path(sys.argv[2]), pathlib.Path(sys.argv[3]), 'build')",
                Path.Combine(repository, "tools/scripts/workflow"), destination, archive]);
            Assert.True(extraction.Exit == 0, extraction.Text);
            Directory.Move(root, offline);
            var received = CommonExecutionEvidence.ValidateBuild(destination, build.Round);
            var producer = SharedBuildContractTests.Process(destination, "dotnet", [CommonExecutionEvidence.LeanProducerPath]);
            Assert.True(producer.Exit == 0, producer.Text);
            Assert.Equal("report utility runtime", producer.Text.Trim());
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
            var restored = SharedBuildContractTests.Process(destination, "dotnet", ["restore", proofProject, "--locked-mode", "-nr:false"]);
            Assert.True(restored.Exit == 0, restored.Text);
            var proof = SharedBuildContractTests.Process(destination, "dotnet",
                ["build", proofProject, "--no-restore", "--no-dependencies", "--configuration", "Release", "-nr:false"]);
            Assert.True(CompilationProof.ValidateCapability(proof.Exit, proof.Text), proof.Text);
            Assert.Equal(build.Materials, CommonExecutionEvidence.ValidateBuild(destination).Materials);
        }
        finally
        {
            if (TemporaryFileSystem.Directory.Exists(offline)) Directory.Move(offline, root);
            TemporaryFileSystem.Directory.Delete(destination, recursive: true);
        }
        // The next candidate explicitly requests a project absent from the seed.
        // Restore the original subset into a clean build and compile just that addition.
        var registration = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(Path.Combine(root, EngineeringRegistrationFixture.Path)))!;
        registration["projects"]!.AsArray().Single(project => project!["path"]!.GetValue<string>() == excludedProject)!["ci"] = true;
        Write(EngineeringRegistrationFixture.Path, registration.ToJsonString());
        SharedBuildContractTests.Git(root, "add", EngineeringRegistrationFixture.Path);
        SharedBuildContractTests.Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "request previously unselected test project");
        foreach (var project in projects.Select(item => "tools/" + item.Item1).Append("tools/tests/Runtime").Append("tools/scripts/report"))
            foreach (var kind in new[] { "bin", "obj" }) Directory.Delete(Path.Combine(root, project, kind), recursive: true);
        Directory.Delete(Path.Combine(root, "build/judge-seed"), recursive: true);
        Cache("restore", "--judge-key", key);
        environment["CI_BUILD_ROUND"] = "";
        var expanded = Stage("expanded-selection", "build");
        Assert.Contains("\"status\": \"installed\"", expanded, StringComparison.Ordinal);
        Assert.Equal(1, Compilers(expanded));
        var expandedBuild = CommonExecutionEvidence.ValidateBuild(root);
        Assert.Equal(new[] { testProject, excludedProject }, expandedBuild.Projects);
        Assert.Contains(excludedProject, CommonBuildOutputs.TestAssemblies(root, expandedBuild).Keys);
        Assert.True(File.Exists(Path.Combine(root, "build/judge-seed/receipts", excludedProject + ".seed.json")));
        Cache("snapshot");
        Cache("restore", "--judge-key", key);
        Write("tools/StrataLint.Cli/Program.cs", "not valid C#\n");
        Stage("wrong-candidate", "build", expected: 1);
        foreach (var path in new[] { CommonExecutionEvidence.BuildPath, CommonExecutionEvidence.EngineeringPath,
                     CommonExecutionEvidence.CurrentPath, CommonExecutionEvidence.TestsPath })
            Assert.False(File.Exists(Path.Combine(root, path)));

        void NarrowPlan()
        {
            var commit = SharedBuildContractTests.Git(root, "rev-parse", "HEAD");
            var entry = SharedBuildContractTests.Git(root, "ls-tree", "HEAD", "--", "global.json").Split([' ', '\t'], StringSplitOptions.RemoveEmptyEntries);
            Write("build/narrow-changes.json", JsonSerializer.Serialize(new { schema_version = 1, mode = "current",
                candidate = new { commit, tree = SharedBuildContractTests.Git(root, "rev-parse", "HEAD^{tree}") }, @base = (string?)null, head = (string?)null,
                complete = true, change_count = 1, changes = new[] { new { status = "A", old = (object?)null, @new = new { path = "global.json", mode = entry[0], oid = entry[2] } } } }));
            Run("python3", "-B", "tools/scripts/workflow/ci.py", "plan", "--repository", physicalRoot,
                "--commit", commit, "--changes", "build/narrow-changes.json", "--output", "build/narrow-plan.json");
            environment["CI_PLAN_PATH"] = "build/narrow-plan.json";
            environment["CI_CHANGES_PATH"] = "build/narrow-changes.json";
        }
        void ResetCompiledOutputs()
        {
            foreach (var project in projects.Select(item => "tools/" + item.Item1).Append("tools/tests/Runtime").Append("tools/scripts/report"))
                foreach (var kind in new[] { "bin", "obj" })
                    if (Directory.Exists(Path.Combine(root, project, kind))) Directory.Delete(Path.Combine(root, project, kind), recursive: true);
            Directory.Delete(Path.Combine(root, "build/judge-seed"), recursive: true);
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
        string[] Calls() => File.ReadAllLines(Path.Combine(root, "build/dotnet-calls"));
        static int ObservedCompilers(string text)
        {
            var rows = text.Split('\n').Where(line => line.StartsWith("JUDGE_CSC ", StringComparison.Ordinal))
                .Select(line => JsonDocument.Parse(line["JUDGE_CSC ".Length..]).RootElement).ToArray();
            Assert.DoesNotContain(rows, row => row.GetProperty("status").GetString() == "unavailable");
            var summaries = rows.Where(row => row.GetProperty("status").GetString() == "complete").ToArray();
            Assert.Equal(2, summaries.Length); // Bootstrap and the one requested fixture build root.
            return summaries.Sum(row => row.GetProperty("count").GetInt32());
        }

        static int Compilers(string text) => Regex.Matches(text,
                @"(?m)^Task Performance Summary:\r?\n(?<tasks>(?:[^\r\n]+\r?\n)*)")
            .SelectMany(summary => Regex.Matches(summary.Groups["tasks"].Value,
                @"(?m)^[^\r\n]*\bCsc[ \t]+(?<calls>[0-9]+)[ \t]+calls\r?$"))
            .Sum(task => int.Parse(task.Groups["calls"].Value, System.Globalization.CultureInfo.InvariantCulture));
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
            var cacheEnvironment = new Dictionary<string, string>(environment) { ["GITHUB_EVENT_NAME"] = "push" };
            var result = SharedBuildContractTests.Process(physicalRoot, "python3",
                new[] { "tools/scripts/worktree/lean_actions.py", command, "--repository", physicalRoot, "--layers", "judge" }.Concat(arguments).ToArray(), cacheEnvironment);
            Assert.True(result.Exit == 0, result.Text);
            if (command == "snapshot") Assert.Contains("judge_ready=true", result.Text, StringComparison.Ordinal);
        }
    }
}
