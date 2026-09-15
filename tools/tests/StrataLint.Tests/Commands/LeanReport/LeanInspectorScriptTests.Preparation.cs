using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanInspectorScriptTests
{
    [Fact]
    public void AcceptedPreparedResultDoesNotRepeatReportSemantics()
    {
        using var fixture = new RuntimeFixture();
        Assert.Equal(0, fixture.Prepare().ExitCode);
        Assert.Equal(0, fixture.Resume().ExitCode);

        var result = ReadPreparedResult(fixture, rejectSemanticValidation: true);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.True(JsonNode.Parse(result.StandardOutput)!["lean_build_succeeded"]!.GetValue<bool>());
    }

    [Theory]
    [InlineData("success", 0)]
    [InlineData("reuse", 0)]
    [InlineData("late-fallback", 0)]
    [InlineData("report", 2)]
    [InlineData("materials", 2)]
    [InlineData("sha", 2)]
    [InlineData("provenance", 2)]
    [InlineData("attestation", 2)]
    [InlineData("seed-schema", 2)]
    [InlineData("seed-partition", 2)]
    [InlineData("seed-runtime_sha256", 2)]
    [InlineData("seed-report_sha256", 2)]
    [InlineData("seed-materials_sha256", 2)]
    public void AcceptedPreparedResultBindsEveryPublishedMember(string scenario, int expectedExit)
    {
        using var fixture = new RuntimeFixture();
        if (scenario is "reuse" or "late-fallback") fixture.Pair("full-fallback", 2);
        Assert.Equal(0, fixture.Prepare().ExitCode);
        if (scenario == "late-fallback")
            File.WriteAllText(Path.Combine(fixture.Preparation, "baseline/raw-lean-report.json.materials.zip"), "lost fixed seed");
        Assert.Equal(0, fixture.Resume().ExitCode);
        if (scenario.StartsWith("seed-", StringComparison.Ordinal))
        {
            var seed = JsonNode.Parse(File.ReadAllText(fixture.Output + ".seed.json"))!;
            seed[scenario[5..]] = scenario.EndsWith("sha256", StringComparison.Ordinal) ? new string('0', 64) : "corrupt";
            File.WriteAllText(fixture.Output + ".seed.json", seed.ToJsonString());
        }
        else if (expectedExit != 0)
        {
            var suffix = scenario switch
            {
                "report" => "", "materials" => ".materials.zip", "sha" => ".sha256",
                "provenance" => ".provenance.json", "attestation" => ".input.attestation",
                _ => throw new InvalidOperationException(scenario),
            };
            File.AppendAllText(fixture.Output + suffix, "corrupt");
        }

        var result = ReadPreparedResult(fixture, rejectSemanticValidation: true);

        Assert.True(result.ExitCode == expectedExit, Encoding.UTF8.GetString(result.StandardError));
        if (expectedExit == 0)
            Assert.Equal(scenario != "reuse", JsonNode.Parse(result.StandardOutput)!["lean_build_succeeded"]!.GetValue<bool>());
    }

    private static ProcessOutput ReadPreparedResult(RuntimeFixture fixture, bool rejectSemanticValidation) =>
        Run("python3", ["-B", "-c", """
            import json, pathlib, sys
            root, directory, report = map(pathlib.Path, sys.argv[1:4])
            sys.path.insert(0, str(root / "tools/lean-inspector"))
            import delta
            def reject(_): raise AssertionError("accepted report semantics were checked again")
            if sys.argv[4] == "true": delta.validate_materials = reject
            from preparation import validate_result
            try:
                print(json.dumps(validate_result(root, directory, report)))
            except (OSError, ValueError, KeyError, TypeError) as error:
                print(str(error), file=sys.stderr)
                sys.exit(2)
            """, fixture.Root, fixture.Preparation, fixture.Output, rejectSemanticValidation ? "true" : "false"], fixture.Root);

    [Fact]
    public void ReportWrapperPreparesAndResumesTheEnvironmentDirectoryWithoutEarlyLakeCache()
    {
        using var fixture = new RuntimeFixture();
        const string relative = "tools/scripts/report/lean-report.sh";
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), relative), Path.Combine(fixture.Root, relative));
        var output = Path.Combine(fixture.Root, ".lake/build/stratalint/raw-lean-report.json");
        var prepared = Invoke("--prepare");
        Assert.True(prepared.ExitCode == 0, Encoding.UTF8.GetString(prepared.StandardError));
        Assert.True(JsonNode.Parse(prepared.StandardOutput)!["needs_lean_build"]!.GetValue<bool>());
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, ".lake")));
        Assert.DoesNotContain("build", fixture.Commands);

        var resumed = Invoke();

        Assert.True(resumed.ExitCode == 0, Encoding.UTF8.GetString(resumed.StandardError));
        Assert.True(File.Exists(output));
        Assert.True(File.Exists(Path.Combine(fixture.Preparation, "result.json")));
        Assert.Contains($"env {Path.Combine(fixture.Root, "runtime/bin/lean")} --run", fixture.Commands);

        ProcessOutput Invoke(params string[] arguments) => Run("env", [
            $"LAKE_BIN={Path.Combine(fixture.Root, "runtime/bin/lean")}",
            $"LEAN_BIN={Path.Combine(fixture.Root, "runtime/bin/lean")}",
            $"STRATALINT_LEAN_REPORT_PREPARATION={fixture.Preparation}",
            "bash", Path.Combine(fixture.Root, relative), .. arguments], fixture.Root);
    }

    [Fact]
    public void PreparedAndOrdinaryReportProductionAreByteIdentical()
    {
        using var fixture = new RuntimeFixture();
        fixture.Pair("full-fallback", 2);
        var report = File.ReadAllBytes(fixture.Output);
        var materials = File.ReadAllBytes(fixture.Output + ".materials.zip");
        Directory.Delete(Path.Combine(fixture.Root, "cache"), recursive: true);
        Assert.Equal(0, fixture.Prepare().ExitCode);
        var resumed = fixture.Resume();
        Assert.True(resumed.ExitCode == 0, Encoding.UTF8.GetString(resumed.StandardError));
        Assert.Equal(report, File.ReadAllBytes(fixture.Output));
        Assert.Equal(materials, File.ReadAllBytes(fixture.Output + ".materials.zip"));
    }

    [Fact]
    public void CustomLakeRequiresExplicitPairedLean()
    {
        using var fixture = new RuntimeFixture();
        var result = Run("env", [$"LAKE_BIN={Path.Combine(fixture.Root, "runtime/bin/lean")}", "LEAN_BIN=",
            Path.Combine(fixture.Root, InspectorScript), "--repository", fixture.Root, "--output", fixture.Output], fixture.Root);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("LEAN_BIN", Encoding.UTF8.GetString(result.StandardError));
        Assert.Empty(fixture.Commands);
    }

    [Fact]
    public void DefaultLeanAndLakeUseTheSameRepositoryPinnedSelector()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new RuntimeFixture();
        fixture.Write("runtime/bin/elan", """
            #!/usr/bin/env python3
            import json, os, pathlib, sys
            root = pathlib.Path.cwd()
            with (root / "selectors").open("a") as stream:
                stream.write(json.dumps([os.environ["ELAN_TOOLCHAIN"], *sys.argv[1:]]) + "\n")
            print(root / "runtime/bin/lean")
            """);
        File.SetUnixFileMode(Path.Combine(fixture.Root, "runtime/bin/elan"), UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var result = Run("env", ["LAKE_BIN=", "LEAN_BIN=", "ELAN_TOOLCHAIN=unrelated-default",
            $"PATH={Path.Combine(fixture.Root, "runtime/bin")}:{Environment.GetEnvironmentVariable("PATH")}",
            "python3", Path.Combine(fixture.Root, "tools/lean-inspector/runtime_identity.py"),
            "--repository", fixture.Root, "--select"], fixture.Root);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var selections = File.ReadAllLines(Path.Combine(fixture.Root, "selectors"))
            .Select(line => JsonNode.Parse(line)!.AsArray().Select(value => value!.ToString()).ToArray()).ToArray();
        Assert.Equal(2, selections.Length);
        Assert.All(selections, selection => Assert.Equal("leanprover/lean4:v4.31.0", selection[0]));
        Assert.Equal(new[] { "lake", "lean" }, selections.Select(selection => selection[2]));
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, ".lake")));
    }

    [Fact]
    public void DeclaredLeanRuntimeCanBeValidatedWithoutLakeOrProjectCache()
    {
        using var fixture = new RuntimeFixture();
        var result = fixture.Runtime(directLean: true);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal("--print-prefix\n", fixture.Commands);
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, ".lake")));
    }

    [Theory]
    [InlineData("missing", true)]
    [InlineData("reuse", false)]
    [InlineData("changed", true)]
    [InlineData("corrupt", true)]
    public void ReportPreparationDefersLeanCacheAndPublishesOnlyOnResume(string seed, bool needsBuild)
    {
        using var fixture = new RuntimeFixture();
        if (seed != "missing") fixture.Pair("full-fallback", 2);
        if (seed == "changed") fixture.Write("D5/Probe.lean", "def probe : Nat := 2\n");
        if (seed == "corrupt")
            foreach (var path in Directory.GetFiles(Path.Combine(fixture.Root, "cache"), "*.materials.zip", SearchOption.AllDirectories))
                File.WriteAllText(path, "corrupt seed");
        if (File.Exists(fixture.Output)) Directory.Delete(Path.GetDirectoryName(fixture.Output)!, recursive: true);
        var priorCommands = fixture.Commands;
        fixture.Write(CacheRunScript, "#!/bin/sh\nmkdir -p .lake\nexec \"$@\"\n");

        var prepared = fixture.Prepare();

        Assert.True(prepared.ExitCode == 0, Encoding.UTF8.GetString(prepared.StandardError));
        var preparation = JsonNode.Parse(Encoding.UTF8.GetString(prepared.StandardOutput))!.AsObject();
        Assert.Single(preparation);
        Assert.Equal(needsBuild, preparation["needs_lean_build"]!.GetValue<bool>());
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, ".lake")), "preparation materialized the Lean project cache");
        Assert.False(File.Exists(fixture.Output), "preparation published a report");
        Assert.DoesNotContain("--run", fixture.Commands[priorCommands.Length..], StringComparison.Ordinal);
        Assert.DoesNotContain("build", fixture.Commands[priorCommands.Length..], StringComparison.Ordinal);

        var resumed = fixture.Resume();

        Assert.True(resumed.ExitCode == 0, Encoding.UTF8.GetString(resumed.StandardError));
        Assert.True(File.Exists(fixture.Output));
        var result = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Preparation, "result.json")))!;
        Assert.Equal("lean-report-preparation-result-v1", result["schema"]!.ToString());
        Assert.Equal(needsBuild, result["lean_build_executed"]!.GetValue<bool>());
        Assert.Equal(needsBuild, result["lean_build_succeeded"]!.GetValue<bool>());
        Assert.Equal(needsBuild ? 1 : 0, fixture.Commands[priorCommands.Length..].Split('\n')
            .Count(line => line.Contains("--run", StringComparison.Ordinal)));
    }

    [Theory]
    [InlineData("source")]
    [InlineData("runtime")]
    [InlineData("plan")]
    [InlineData("descriptor")]
    [InlineData("missing")]
    public void PreparedReportRejectsChangedInputsBeforeAnyProduction(string changed)
    {
        using var fixture = new RuntimeFixture();
        var prepared = fixture.Prepare();
        Assert.True(prepared.ExitCode == 0, Encoding.UTF8.GetString(prepared.StandardError));
        if (changed == "source") fixture.Write("D5/Probe.lean", "def probe : Nat := 3\n");
        if (changed == "runtime") fixture.Write("runtime/lib/lean/Declared.olean", "different runtime");
        if (changed == "plan") File.WriteAllText(Path.Combine(fixture.Preparation, "delta-plan.json"), "{}");
        if (changed == "descriptor") File.WriteAllText(Path.Combine(fixture.Preparation, "preparation.json"), "{}");
        if (changed == "missing") Directory.Delete(fixture.Preparation, recursive: true);

        var result = fixture.Resume();

        Assert.Equal(2, result.ExitCode);
        Assert.DoesNotContain("--run", fixture.Commands, StringComparison.Ordinal);
        Assert.DoesNotContain("build", fixture.Commands, StringComparison.Ordinal);
        Assert.False(File.Exists(fixture.Output));
        Assert.False(File.Exists(Path.Combine(fixture.Preparation, "result.json")));
    }

    [Fact]
    public void PreparedReportKeepsItsSeedWhenOriginalCacheIsReplaced()
    {
        using var fixture = new RuntimeFixture();
        fixture.Pair("full-fallback", 2);
        Assert.Equal(0, fixture.Prepare().ExitCode);
        Directory.Delete(Path.Combine(fixture.Root, "cache"), recursive: true);
        var before = fixture.Commands;

        var result = fixture.Resume();

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.DoesNotContain("build", fixture.Commands[before.Length..], StringComparison.Ordinal);
        Assert.DoesNotContain("--run", fixture.Commands[before.Length..], StringComparison.Ordinal);
    }

    [Fact]
    public void FailedPreparedRetryCannotRetainPriorSuccessfulBuildEvidence()
    {
        using var fixture = new RuntimeFixture();
        Assert.Equal(0, fixture.Prepare().ExitCode);
        Assert.Equal(0, fixture.Resume().ExitCode);
        Assert.True(File.Exists(Path.Combine(fixture.Preparation, "result.json")));
        fixture.Write("D5/Probe.lean", "def probe : Nat := 42\n");
        var before = fixture.Commands;

        var result = fixture.Resume();

        Assert.Equal(2, result.ExitCode);
        Assert.False(File.Exists(Path.Combine(fixture.Preparation, "result.json")));
        Assert.DoesNotContain("build", fixture.Commands[before.Length..]);
    }

    [Fact]
    public void PreparedReportFallsBackWhenFixedSeedMaterialIsLost()
    {
        using var fixture = new RuntimeFixture();
        fixture.Pair("full-fallback", 2);
        Assert.Equal(0, fixture.Prepare().ExitCode);
        File.WriteAllText(Path.Combine(fixture.Preparation, "baseline/raw-lean-report.json.materials.zip"), "damaged after preparation");
        var before = fixture.Commands;

        var result = fixture.Resume();

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("build", fixture.Commands[before.Length..], StringComparison.Ordinal);
        Assert.Contains("--run", fixture.Commands[before.Length..], StringComparison.Ordinal);
    }
}
