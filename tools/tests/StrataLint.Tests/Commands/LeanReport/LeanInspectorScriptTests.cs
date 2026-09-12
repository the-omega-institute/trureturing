using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanInspectorScriptTests
{
    private const string InspectorScript = "tools/lean-inspector/inspect.sh";
    private const string InspectorSource = "tools/lean-inspector/Inspector.lean";
    private const string MaterialCompactor = "tools/lean-inspector/materials.py";
    private const string InputScript = "tools/scripts/report/lean-report-input.sh";
    private const string ResourceObservationLibrary = "tools/scripts/lib/resource-observation-lib.sh";
    private const string CacheRunScript = "tools/scripts/worktree/lean-cache-run.sh";

    [Fact]
    public void ExactSeedStillEntersLakeAndIncrementalProducer() =>
        LeanSeedProcessContract.Run("InspectorTests.test_inspector_runs_lake_on_exact_seed_with_zero_reinspection");

    [Fact]
    public void LakeAndInspectorFailuresKeepTheirRealExitCodes() =>
        LeanSeedProcessContract.Run("InspectorTests.test_inspector_real_failure_blocks_even_when_report_seed_exists");

    [Fact]
    public void DeltaReinspectionPreservesDependencyAndMaterialContracts() => LeanSeedProcessContract.Run("DeltaTests");

    [Fact]
    public void ReportStagingDoesNotPreemptColdCacheProvisioning() =>
        LeanSeedProcessContract.Run("InspectorTests.test_report_staging_does_not_preempt_cold_cache_provisioning");

    [Fact]
    public void DeclaredRuntimeDependenciesInvalidateModuleResults() =>
        LeanSeedProcessContract.Run("InspectorTests.test_declared_runtime_material_change_reinspects_inside_same_partition");

    [Theory]
    [InlineData("standalone", 0)]
    [InlineData("prebuilt", 0)]
    [InlineData("missing-prebuilt", 2)]
    public void InspectorDefaultsToCompleteModuleEnumeration(string cliMode, int expectedExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var repository = CreateRepository(temporary.Path);
        var lake = Path.Combine(temporary.Path, "runtime/bin/lean");
        Directory.CreateDirectory(Path.GetDirectoryName(lake)!);
        File.WriteAllText(lake, "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> \"$STUB_LOG\"\nif [[ \"$*\" == \"env lean --print-prefix\" ]]; then dirname \"$(dirname \"$0\")\"; exit 0; fi\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var log = Path.Combine(temporary.Path, "lake.log");
        var output = Path.Combine(temporary.Path, "report.json");
        var cli = Path.Combine(repository, "tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll");
        if (cliMode == "prebuilt")
        {
            var build = Run("dotnet", ["build", "tools/StrataLint.Lean/StrataLint.Lean.csproj", "--configuration", "Release"], repository);
            Assert.True(build.ExitCode == 0, Encoding.UTF8.GetString(build.StandardOutput) + Encoding.UTF8.GetString(build.StandardError));
            File.WriteAllText(Path.Combine(repository, "tools/StrataLint.Lean/Fixture.cs"), "invalid source forbids a repeated build");
        }

        var full = Run("env", [$"LAKE_BIN={lake}", $"STUB_LOG={log}",
            $"STRATALINT_LEAN_PRODUCER_DLL={(cliMode == "standalone" ? "" : cli)}",
            Path.Combine(repository, InspectorScript), "--repository", repository, "--output", output], repository);
        Assert.True(full.ExitCode == expectedExit, Encoding.UTF8.GetString(full.StandardError));
        if (expectedExit != 0)
        {
            Assert.Contains("candidate producer is absent", Encoding.UTF8.GetString(full.StandardError), StringComparison.Ordinal);
            Assert.False(File.Exists(output));
            return;
        }
        Assert.Equal("[]", File.ReadAllText(output + ".logs/utility-input.stdout.log").Trim());
        var fullInspect = File.ReadAllLines(log).Single(static line => line.Contains(" --output ", StringComparison.Ordinal));
        Assert.Contains("Trureturing Trureturing.lean sha256:", fullInspect, StringComparison.Ordinal);
        Assert.Contains("D5.Probe D5/Probe.lean sha256:", fullInspect, StringComparison.Ordinal);
    }


    private static ProcessOutput Run(string command, IReadOnlyList<string> arguments, string cwd) =>
        TestProcessRunner.Run(command, arguments, cwd, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);

    private static string CreateRepository(string temporary)
    {
        var repository = Path.Combine(temporary, "repo");
        var root = TestRepositoryLayout.FindRoot();
        Write(repository, "Trureturing.lean", "import D5.Probe\n");
        Write(repository, "D5/Probe.lean", "def probe : Nat := 1\n");
        foreach (var relative in new[]
            { InspectorScript, InspectorSource, MaterialCompactor, InputScript, ResourceObservationLibrary,
                "tools/scripts/worktree/lean-cache-input.sh", "tools/scripts/worktree/lean_cache.py",
                "tools/scripts/report/producer_paths.py", "tools/scripts/report/dotnet_producer.py",
                "tools/lean-inspector/delta.py", "tools/lean-inspector/runtime_identity.py",
                "tools/lean-inspector/report_cache.py" })
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(repository, relative))!);
            File.Copy(Path.Combine(root, relative), Path.Combine(repository, relative));
        }
        InstallCacheRun(repository);
        InstallProducerInputs(repository);
        return repository;
    }

    private static void InstallProducerInputs(string repository)
    {
        Write(repository, "global.json", File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "global.json")));
        string[] projects = ["StrataLint.Lean", "StrataLint.Engine", "Trureturing.Truth"];
        foreach (var project in projects)
        {
            Write(repository, $"tools/{project}/{project}.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(repository, $"tools/{project}/Fixture.cs", "// fixture\n");
        }
        Write(repository, "tools/StrataLint.Lean/StrataLint.Lean.csproj",
            "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><OutputType>Exe</OutputType>"
            + "<TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>\n");
        Write(repository, "tools/StrataLint.Lean/Fixture.cs", "System.Console.WriteLine(\"[]\");\n");
        Write(repository, "tools/scripts/lean-report-pair.sh", "#!/usr/bin/env bash\n");
        Write(repository, "tools/scripts/worktree/lean-cache-publish.sh", "#!/usr/bin/env bash\n");
        Write(repository, "tools/scripts/workflow/scribe-content-checks.sh", "#!/usr/bin/env bash\n");
        Write(repository, "lean-toolchain", "leanprover/lean4:v4.31.0\n");
        Write(repository, "lakefile.toml", "name = \"Fixture\"\n");
        Write(repository, "lake-manifest.json",
            "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789abcdef0123456789abcdef01234567\"}]}\n");
        Write(repository, "Meta/engineering-projects.json", JsonSerializer.Serialize(new
        {
            version = 1, projects = projects.Select(name => new
            {
                path = $"tools/{name}/{name}.csproj", assembly = name, role = "test-support", ci = false,
                include = new[] { $"tools/{name}/Fixture.cs" }, exclude = Array.Empty<string>(),
                references = Array.Empty<string>(), owner = (object?)null, owned_test_assembly = (string?)null,
                test_partition = (string?)null,
                build_inputs = new[] { "global.json" }, execution_inputs = (string[]?)null,
                execution_excludes = (string[]?)null, execution_environment = (string[]?)null,
                root_namespace = "Fixture", namespace_exclude = Array.Empty<string>(), global_namespace_exceptions = Array.Empty<string>(),
            }), historical_projects = Array.Empty<object>(), rule_build_inputs = Array.Empty<string>(),
        }));
        Write(repository, "Meta/ReportProducers/lean-report.json", JsonSerializer.Serialize(new
        {
            schema = "report-producer-scope-v1", runtime = new { lean = new[] { "bin/lean" }, python = new[] { "executable" } }, projects = new[] { "tools/StrataLint.Lean/StrataLint.Lean.csproj" },
            materials = new[] { "global.json" }, scripts = new[]
            {
                InspectorScript, InspectorSource, MaterialCompactor, InputScript, ResourceObservationLibrary, CacheRunScript,
                "tools/scripts/worktree/lean-cache-input.sh", "tools/scripts/worktree/lean_cache.py",
                "tools/scripts/report/producer_paths.py", "tools/scripts/report/dotnet_producer.py",
                "tools/lean-inspector/delta.py", "tools/lean-inspector/runtime_identity.py", "tools/lean-inspector/report_cache.py",
            },
        }));
        Write(repository, ".gitignore", "**/bin/\n**/obj/\n**/__pycache__/\n");
        Assert.Equal(0, Run("git", ["init", "--quiet"], repository).ExitCode);
        Assert.Equal(0, Run("git", ["add", "."], repository).ExitCode);
    }

    private static void Write(string root, string relative, string contents)
    {
        var path = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, contents, new UTF8Encoding(false));
    }

    private static void InstallCacheRun(string repository)
    {
        if (OperatingSystem.IsWindows()) return;
        Write(repository, CacheRunScript, "#!/usr/bin/env bash\nexec \"$@\"\n");
        File.SetUnixFileMode(
            Path.Combine(repository, CacheRunScript),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
