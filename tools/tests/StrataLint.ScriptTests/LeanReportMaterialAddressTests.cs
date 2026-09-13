using System.Text.Json;
using Xunit.Abstractions;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class LeanReportMaterialAddressTests(ITestOutputHelper output)
{
    [Fact]
    public void RealLakeConfigPreservesStdoutAndWritesIdenticalJsonToFile()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseNativeLean();
        var config = Path.Combine(fixture.Repository, "config output.json");
        var stdout = fixture.ReadNativeConfig("lakefile.toml");
        var file = fixture.ReadNativeConfig("lakefile.toml", "--output", config);

        fixture.Success(stdout);
        fixture.Success(file);
        Assert.Empty(file.Stdout);
        Assert.Equal(stdout.Stdout, File.ReadAllText(config));
        using var parsed = JsonDocument.Parse(stdout.Stdout);
        Assert.Equal(new[] { "Trureturing", "LeanInformationAudit" }, parsed.RootElement
            .GetProperty("defaultTargets").EnumerateArray().Select(target => target.GetString()));
    }

    [Theory]
    [InlineData("parse")]
    [InlineData("read")]
    [InlineData("write")]
    [InlineData("arguments")]
    public void RealLakeConfigInputAndOutputFailuresRemainNonzero(string failure)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseNativeLean();
        fixture.WriteSource("invalid.toml", "name = [\n");
        var destination = Path.Combine(fixture.Repository, "config output.json");
        var source = failure == "parse" ? "invalid.toml" : failure == "read" ? "absent.toml" : "lakefile.toml";
        var arguments = failure == "arguments" ? new[] { source, "--output" }
            : new[] { source, "--output", failure == "write" ? fixture.Repository : destination };

        var result = fixture.ReadNativeConfig(arguments);

        Assert.NotEqual(0, result.ExitCode);
        Assert.False(File.Exists(destination));
    }

    [Fact]
    public void RealLeanDeltaBuildCompilesDependenciesExternalClaimAndAllAuditRootsWithIdenticalFullBytes()
    {
        if (OperatingSystem.IsWindows()) return;
        var discovery = TestProcessRunner.Run("elan", ["which", "lake"], TestRepositoryLayout.FindRoot(),
            StrataLint.Engine.BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(0, discovery.ExitCode);
        var lake = System.Text.Encoding.UTF8.GetString(discovery.StandardOutput).Trim();
        using var fixture = new LeanReportTransportFixture();
        fixture.UseNativeLean();
        fixture.Success(fixture.MakeNativeReport(lake));
        Assert.Single(fixture.UtilityCalls);
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\ntheorem result : ¬ False := fun h => h\n-- current delta\n");
        var build = Path.Combine(fixture.Repository, ".lake/build");
        StrataLint.TestSupport.TemporaryFileSystem.Directory.Delete(build, true);

        var delta = fixture.MakeNativeReport(lake);

        fixture.Success(delta);
        Assert.Equal(2, fixture.UtilityCalls.Length);
        Assert.StartsWith("LEAN_CACHE ", fixture.Phase("delta-config", "stdout"), StringComparison.Ordinal);
        Assert.Contains("LEAN_REPORT_DELTA mode=delta", delta.Text, StringComparison.Ordinal);
        Assert.Equal("build +D5.External +Trureturing LeanInformationAudit", fixture.BuildCalls[^1]);
        foreach (var module in new[] { "Trureturing", "D5/Probe", "D5/External", "LeanInformationAudit/One", "LeanInformationAudit/Two" })
            Assert.True(File.Exists(Path.Combine(build, "lib/lean", module + ".olean")), module);
        Assert.False(File.Exists(Path.Combine(build, "lib/lean/D5/Unchanged.olean")));
        var reportBytes = File.ReadAllBytes(fixture.Output);
        var materialBytes = File.ReadAllBytes(fixture.Output + ".materials.zip");
        using (var report = JsonDocument.Parse(reportBytes))
        {
            var root = report.RootElement.GetProperty("modules").EnumerateArray()
                .Single(module => module.GetProperty("module").GetString() == "Trureturing");
            Assert.True(root.GetProperty("utility_refutation").GetProperty("is_closed_negation").GetBoolean());
            Assert.Equal(4, report.RootElement.GetProperty("modules").GetArrayLength());
        }
        fixture.Success(fixture.Validate(fixture.Output));
        fixture.Success(fixture.Input("verify", "--repository", fixture.Repository, "--report", fixture.Output));
        fixture.ClearCache();

        fixture.Success(fixture.MakeNativeReport(lake));

        Assert.Equal("build", fixture.BuildCalls[^1]);
        Assert.Equal(3, fixture.UtilityCalls.Length);
        Assert.True(File.Exists(Path.Combine(build, "lib/lean/D5/Unchanged.olean")));
        Assert.Equal(reportBytes, File.ReadAllBytes(fixture.Output));
        Assert.Equal(materialBytes, File.ReadAllBytes(fixture.Output + ".materials.zip"));
        fixture.Success(fixture.Validate(fixture.Output));
        fixture.Success(fixture.Input("verify", "--repository", fixture.Repository, "--report", fixture.Output));

        // A provisional plan can survive baseline metadata checks while its
        // material archive is unusable. Full demand must precede full inspection.
        File.WriteAllText(fixture.CachedReport + ".materials.zip", "invalid optional archive");
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\ntheorem result : ¬ False := fun h => h\n-- material fallback\n");
        StrataLint.TestSupport.TemporaryFileSystem.Directory.Delete(build, true);
        var recovered = fixture.MakeNativeReport(lake);
        fixture.Success(recovered);
        Assert.Equal(4, fixture.UtilityCalls.Length);
        Assert.Contains("LEAN_REPORT_DELTA mode=full-fallback", recovered.Text, StringComparison.Ordinal);
        Assert.Equal(new[] { "build +D5.External +Trureturing LeanInformationAudit", "build" }, fixture.BuildCalls.TakeLast(2));
        Assert.Equal("0", fixture.Phase("delta-build", "exit"));
        Assert.Equal("0", fixture.Phase("fallback-build", "exit"));
        Assert.True(File.Exists(Path.Combine(build, "lib/lean/D5/Unchanged.olean")));
        fixture.Success(fixture.Validate(fixture.Output));

        var buildsBeforeFailure = fixture.BuildCalls.Length;
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\ntheorem result : False := True.intro\n");
        var failed = fixture.MakeNativeReport(lake);
        output.WriteLine("Native delta failure: make_exit={0}; delta_build_exit={1}",
            failed.ExitCode, fixture.Phase("delta-build", "exit"));
        Assert.Equal(2, failed.ExitCode);
        // The canonical reader preserves Lake's failure status; make exits 2.
        Assert.Contains("LEAN_INSPECTOR_FAILED phase=delta-build exit=1", failed.Text, StringComparison.Ordinal);
        Assert.Equal(buildsBeforeFailure + 1, fixture.BuildCalls.Length);
        Assert.DoesNotContain("RAW_LEAN_REPORT", failed.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void RealLeanLibraryDefaultFacetIsRetainedBeforeFullInspection()
    {
        if (OperatingSystem.IsWindows()) return;
        var discovery = TestProcessRunner.Run("elan", ["which", "lake"], TestRepositoryLayout.FindRoot(),
            StrataLint.Engine.BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(0, discovery.ExitCode);
        var lake = System.Text.Encoding.UTF8.GetString(discovery.StandardOutput).Trim();
        using var fixture = new LeanReportTransportFixture();
        fixture.UseNativeLean();
        fixture.SetBuildConfiguration("defaultFacets = [\"static\"]");
        fixture.Success(fixture.MakeNativeReport(lake));
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\ntheorem result : ¬ False := fun h => h\n-- default facet\n");
        var build = Path.Combine(fixture.Repository, ".lake/build");
        StrataLint.TestSupport.TemporaryFileSystem.Directory.Delete(build, true);

        var result = fixture.MakeNativeReport(lake);

        fixture.Success(result);
        Assert.Contains("LEAN_REPORT_DELTA mode=full-fallback", result.Text, StringComparison.Ordinal);
        Assert.Equal(new[] { "build", "build" }, fixture.BuildCalls);
        Assert.Single(StrataLint.TestSupport.TemporaryFileSystem.Directory.EnumerateFiles(
            Path.Combine(build, "lib"), "*.a", SearchOption.AllDirectories));
        Assert.True(File.Exists(Path.Combine(build, "lib/lean/D5/Unchanged.olean")));
        fixture.Success(fixture.Validate(fixture.Output));
    }

    [Fact]
    public void SelectedBuildFailureRemainsFatalWithoutFullRecovery()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        fixture.Success(fixture.MakeInspectedReport());
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\n-- selected failure\n");

        var result = fixture.Inspect("FIXTURE_BUILD_EXIT=71");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(2, fixture.BuildCalls.Length);
        Assert.Equal(2, fixture.UtilityCalls.Length);
        Assert.Equal(new[] { "build", "inspect", "build" }, fixture.Events);
        Assert.Equal("71", fixture.Phase("delta-build", "exit"));
    }

    [Fact]
    public void DeltaBuildProjectsSelectedModulesClaimsAndConfiguredDefaultsOnce()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        fixture.SetBuildConfiguration(extraDefault: true);
        fixture.Success(fixture.MakeInspectedReport());
        Assert.Single(fixture.BuildCalls);
        Assert.Single(fixture.UtilityCalls);

        fixture.SetUtilityInput(
            """
            [{"modulePath":"Trureturing.lean","claimGid":"gid","claimModule":"D5.External.Law","claimSelector":"claim","claimSourcePath":"D5/External/Law.lean","claimSourceSha256":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","resultGid":"result","resultModule":"Trureturing","resultSelector":"result"},
             {"modulePath":"D5/Probe.lean","claimGid":"unused","claimModule":"D5.Unselected.Claim","claimSelector":"claim","claimSourcePath":"D5/Unselected/Claim.lean","claimSourceSha256":"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","resultGid":"other","resultModule":"D5.Probe","resultSelector":"other"}]
            """);
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\n-- selected delta\n");

        fixture.Success(fixture.Inspect());
        Assert.Equal(2, fixture.BuildCalls.Length);
        Assert.Equal(2, fixture.UtilityCalls.Length);
        var projected = fixture.BuildCalls[1].Split(' ', StringSplitOptions.RemoveEmptyEntries);
        Assert.Contains("+D5.External.Law", projected);
        Assert.DoesNotContain("+D5.Unselected.Claim", projected);
        Assert.Contains("+Trureturing", projected);
        Assert.Contains("LeanInformationAudit", projected);
        Assert.DoesNotContain("Trureturing", projected);
        Assert.Contains("D5.Probe", projected);
        Assert.Equal(projected.Skip(1).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal), projected.Skip(1));
    }

    [Theory]
    [InlineData("default-facet")]
    [InlineData("lean-configuration")]
    public void UnsupportedProjectionBuildsDefaultsBeforeFullInspection(string configuration)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        if (configuration == "default-facet") fixture.SetBuildConfiguration("defaultFacets = [\"static\"]");
        else fixture.WriteSource("lakefile.lean", "-- alternate configuration\n");
        fixture.Success(fixture.MakeInspectedReport());
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\n-- changed\n");

        fixture.Success(fixture.Inspect());

        Assert.Equal(new[] { "build", "build" }, fixture.BuildCalls);
        Assert.Equal(new[] { "D5.Probe", "Trureturing" }, fixture.ExtractedModules[^1].Order(StringComparer.Ordinal));
    }

    [Theory]
    [InlineData("invalid-json", false)]
    [InlineData("invalid-json", true)]
    [InlineData("missing-output", false)]
    [InlineData("missing-output", true)]
    [InlineData("command-failure", false)]
    [InlineData("command-failure", true)]
    public void UnavailableConfigProjectionRequiresDefaultBuildBeforeFullInspection(string failure, bool buildFails)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        fixture.Success(fixture.MakeInspectedReport());
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\n-- config output failure\n");
        if (failure == "invalid-json") fixture.SetConfigOutput("{");
        // A failed producer must not reuse an output left by an earlier phase.
        File.WriteAllText(fixture.Output + ".logs/delta-config.json", "{\"defaultTargets\":[\"Trureturing\"],"
            + "\"lean_lib\":[{\"name\":\"Trureturing\",\"roots\":[\"Trureturing\",\"D5\"],\"globs\":[\"Trureturing\",\"D5.+\"]}]}");

        var result = fixture.Inspect("FIXTURE_CONFIG_EXIT=" + (failure == "command-failure" ? "75" : "0"),
            "FIXTURE_CONFIG_MISSING_OUTPUT=" + (failure == "missing-output" ? "1" : "0"),
            "FIXTURE_DEFAULT_BUILD_EXIT=" + (buildFails ? "73" : "0"));

        if (buildFails) Assert.NotEqual(0, result.ExitCode); else fixture.Success(result);
        Assert.Equal(new[] { "build", "build" }, fixture.BuildCalls);
        Assert.Equal(buildFails ? new[] { "build", "inspect", "build" }
            : new[] { "build", "inspect", "build", "inspect" }, fixture.Events);
        if (!buildFails)
            Assert.Equal(new[] { "D5.Probe", "Trureturing" }, fixture.ExtractedModules[^1].Order(StringComparer.Ordinal));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SubsetFailureRequiresSuccessfulDefaultBuildBeforeFullInspection(bool buildFails)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        fixture.Success(fixture.MakeInspectedReport());
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\n-- changed\n");

        var result = fixture.Inspect("FIXTURE_INSPECT_EXIT_ONCE=72",
            "FIXTURE_DEFAULT_BUILD_EXIT=" + (buildFails ? "73" : "0"));

        if (buildFails) Assert.NotEqual(0, result.ExitCode); else fixture.Success(result);
        Assert.Equal(3, fixture.BuildCalls.Length);
        Assert.Equal("build", fixture.BuildCalls[^1]);
        Assert.Equal(buildFails
            ? new[] { "build", "inspect", "build", "inspect", "build" }
            : new[] { "build", "inspect", "build", "inspect", "build", "inspect" }, fixture.Events);
        Assert.Equal("0", fixture.Phase("delta-build", "exit"));
        Assert.Equal(buildFails ? "73" : "0", fixture.Phase("fallback-build", "exit"));
        Assert.Contains("+Trureturing", fixture.Phase("delta-build", "command"), StringComparison.Ordinal);
        Assert.DoesNotContain("+Trureturing", fixture.Phase("fallback-build", "command"), StringComparison.Ordinal);
        Assert.Equal(2, fixture.UtilityCalls.Length);
    }

    [Theory]
    [InlineData("{}", false)]
    [InlineData("[{\"modulePath\":\"Trureturing.lean\",\"claimModule\":\"Claim\"}]", false)]
    [InlineData("[]", true)]
    public void AuthoritativeUtilityFailureIsFatalBeforeSelectedBuild(string utility, bool commandFails)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        fixture.Success(fixture.MakeInspectedReport());
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\n-- changed\n");
        fixture.SetUtilityInput(utility);

        var result = fixture.Inspect("FIXTURE_UTILITY_EXIT=" + (commandFails ? "74" : "0"));

        Assert.NotEqual(0, result.ExitCode);
        Assert.Single(fixture.BuildCalls);
        Assert.Single(fixture.ExtractedModules);
    }

    [Fact]
    public void InspectorScriptIdentityChangeRejectsOldSeedWithoutRelabeling()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        fixture.Success(fixture.MakeInspectedReport());
        var before = fixture.ReadInspectorInputs();
        var baseline = fixture.CachedReport;
        var original = LeanReportTransportFixture.Suffixes.ToDictionary(suffix => suffix, suffix => File.ReadAllBytes(baseline + suffix));
        fixture.ChangeCompatibility("producer");
        var after = fixture.ReadInspectorInputs();
        Assert.NotEqual(before.Producer, after.Producer);
        Assert.NotEqual(before.Pair, after.Pair);
        Assert.Equal(2, fixture.Input("verify", "--repository", fixture.Repository, "--report", baseline).ExitCode);

        var result = fixture.MakeInspectedReport();

        fixture.Success(result);
        Assert.Contains("LEAN_REPORT_DELTA_PLAN mode=fallback", result.Text, StringComparison.Ordinal);
        Assert.Equal(new[] { "build", "build" }, fixture.BuildCalls);
        foreach (var (suffix, bytes) in original) Assert.Equal(bytes, File.ReadAllBytes(baseline + suffix));
    }

    [Theory]
    [InlineData("exact")]
    [InlineData("reuse")]
    [InlineData("zero-recheck")]
    public void NonSelectedModesKeepTheirExistingBuildDemand(string mode)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        if (mode == "zero-recheck") fixture.AddIndependentRemovedModule();
        fixture.Success(fixture.MakeInspectedReport());
        if (mode == "zero-recheck") File.Delete(Path.Combine(fixture.Repository, "D5/Removed.lean"));

        // The producer's reuse mode is exercised directly with a distinct
        // requested address; the existing baseline identity is left intact.
        var result = mode == "reuse" ? fixture.InspectReuse(fixture.ReadInspectorInputs()) : fixture.MakeInspectedReport();

        fixture.Success(result);
        Assert.Equal(mode == "exact" ? new[] { "build" } : new[] { "build", "build" }, fixture.BuildCalls);
        Assert.Single(fixture.ExtractedModules);
        Assert.Single(fixture.UtilityCalls);
        if (mode == "reuse") Assert.Contains("LEAN_REPORT_DELTA mode=reuse", result.Text, StringComparison.Ordinal);
        if (mode == "zero-recheck") Assert.Contains("LEAN_REPORT_DELTA mode=delta changed=0 added=0 removed=1 recheck=0", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("exact", false)]
    [InlineData("exact", true)]
    [InlineData("inspector-source", false)]
    [InlineData("inspector-source", true)]
    [InlineData("delta", false)]
    [InlineData("delta", true)]
    public void CacheSelectionRequiresCurrentInputsAndAddressConsistentMaterial(string mode, bool tampered)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        fixture.Success(fixture.MakeInspectedReport());
        var before = fixture.ReadInspectorInputs();
        var baseline = fixture.CachedReport;
        var original = Snapshot(baseline);
        fixture.Success(fixture.Validate(baseline));
        fixture.Success(fixture.Input("verify", "--repository", fixture.Repository, "--report", baseline));
        Assert.Equal(new[] { "D5.Probe", "Trureturing" }, Assert.Single(fixture.ExtractedModules).Order(StringComparer.Ordinal));
        // The unchanged D5.Probe material has a distinct address: the changed
        // Trureturing subset cannot satisfy the baseline material copy by alias.
        using (var report = JsonDocument.Parse(original[""]))
        {
            var keys = report.RootElement.GetProperty("modules").EnumerateArray()
                .Select(module => module.GetProperty("declarations")[0].GetProperty("type_sha256").GetString()).ToArray();
            Assert.Equal(2, keys.Distinct(StringComparer.Ordinal).Count());
        }
        if (mode != "exact")
        {
            var source = mode == "inspector-source" ? LeanReportTransportFixture.AuxiliarySource : "Trureturing.lean";
            fixture.WriteSource(source, File.ReadAllText(Path.Combine(fixture.Repository, source)) + "-- source delta\n");
        }
        var after = fixture.ReadInspectorInputs();
        Assert.Equal(mode != "inspector-source", before.Producer == after.Producer);
        Assert.Equal(mode != "inspector-source", before.Resident == after.Resident);
        Assert.Equal(before.Config, after.Config);
        Assert.Equal(before.Modules, after.Modules);
        Assert.Equal(mode == "exact", before.Pair == after.Pair);
        Assert.Equal(mode != "delta", before.Hashes.SequenceEqual(after.Hashes));
        Assert.Equal(new[] { baseline }, fixture.CacheEntries);
        if (mode != "exact")
        {
            Assert.NotEqual(before.Sources, after.Sources);
            Assert.NotEqual(before.Repository, after.Repository);
            Assert.False(File.Exists(fixture.CachedReport));
            var stale = fixture.Input("verify", "--repository", fixture.Repository, "--report", baseline);
            Assert.Equal(2, stale.ExitCode);
            Assert.Contains(mode == "inspector-source"
                ? "raw Lean report producer is stale for current repository inputs"
                : "raw Lean report is stale for current repository inputs", stale.Text, StringComparison.Ordinal);
        }
        if (tampered) fixture.TamperMaterial(baseline);
        AssertNonmaterial(original, baseline);
        var injected = File.ReadAllBytes(baseline + ".materials.zip");
        var validation = fixture.Validate(baseline);
        var result = fixture.MakeInspectedReport();
        fixture.Success(result);
        var liveValidation = fixture.Validate(fixture.Output);
        var cacheValidation = fixture.Validate(fixture.CachedReport);
        var liveInput = fixture.Input("verify", "--repository", fixture.Repository, "--report", fixture.Output);
        var cacheInput = fixture.Input("verify", "--repository", fixture.Repository, "--report", fixture.CachedReport);
        var sameMaterialBytes = injected.SequenceEqual(File.ReadAllBytes(fixture.Output + ".materials.zip"));
        output.WriteLine("P1 mode={0} tampered={1}; baseline_validate={2}; make_exit={3}; extractions={4}; injected_material_bytes_equal={5}; live/cache_validate={6}/{7}; live/cache_input={8}/{9}; final={10}",
            mode, tampered, validation.ExitCode, result.ExitCode, JsonSerializer.Serialize(fixture.ExtractedModules),
            sameMaterialBytes, liveValidation.ExitCode, cacheValidation.ExitCode, liveInput.ExitCode, cacheInput.ExitCode,
            string.Join(" | ", result.Text.Split('\n').Where(line => line.StartsWith("LEAN_REPORT_DELTA", StringComparison.Ordinal)
                || line.Contains("mode=local-exact", StringComparison.Ordinal))));
        if (mode != "exact")
        {
            AssertNonmaterial(original, baseline);
            Assert.Equal(injected, File.ReadAllBytes(baseline + ".materials.zip"));
            var counts = mode == "inspector-source" ? "changed=0 added=0 removed=0 recheck=0" : "changed=1 added=0 removed=0 recheck=1";
            var planMode = mode == "inspector-source" ? "fallback" : "delta";
            var productionMode = mode == "inspector-source" || tampered ? "full-fallback" : "delta";
            Assert.Contains($"LEAN_REPORT_DELTA_PLAN mode={planMode} {counts}", result.Text, StringComparison.Ordinal);
            Assert.Contains($"LEAN_REPORT_DELTA mode={productionMode} {counts}", result.Text, StringComparison.Ordinal);
        }
        else Assert.Contains(tampered ? "status=miss reason=local-entry-unavailable" : "status=hit mode=local-exact",
            result.Text, StringComparison.Ordinal);
        Assert.Equal(tampered ? 1 : 0, validation.ExitCode);
        if (tampered) Assert.Contains("statement material address mismatch", validation.Text, StringComparison.Ordinal);
        var expectedExtractions = 1 + (mode != "exact" || tampered ? 1 : 0) + (mode == "delta" && tampered ? 1 : 0);
        Assert.Equal(expectedExtractions, fixture.ProducerCalls.Length);
        Assert.Equal(expectedExtractions, fixture.ExtractedModules.Length);
        if (mode == "delta")
        {
            Assert.Equal(tampered ? 3 : 2, fixture.BuildCalls.Length);
            if (tampered) Assert.Equal("build", fixture.BuildCalls[^1]);
            if (tampered)
                Assert.Equal(new[] { "build", "inspect", "build", "inspect", "build", "inspect" }, fixture.Events);
        }
        if (mode == "delta") Assert.Equal(new[] { "Trureturing" }, fixture.ExtractedModules[1]);
        if (mode == "inspector-source" || tampered)
            Assert.Equal(new[] { "D5.Probe", "Trureturing" }, fixture.ExtractedModules[^1].Order(StringComparer.Ordinal));
        fixture.Success(liveValidation);
        fixture.Success(cacheValidation);
        fixture.Success(liveInput);
        fixture.Success(cacheInput);
        Assert.Equal(original[".materials.zip"], File.ReadAllBytes(fixture.Output + ".materials.zip"));
        Assert.Equal(original[".materials.zip"], File.ReadAllBytes(fixture.CachedReport + ".materials.zip"));
        if (mode != "delta") Assert.Equal(original[""], File.ReadAllBytes(fixture.Output));
        Assert.Empty(fixture.ReleaseCalls);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void TransportChecksMaterialAddressesInsideAValidOuterDigest(bool tampered)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        fixture.Success(fixture.MakeInspectedReport());
        var original = Snapshot(fixture.Output);
        var result = fixture.ExerciseMaterialTransport(tampered);
        output.WriteLine(result.Stdout);
        fixture.Success(result);
        foreach (var (suffix, bytes) in original) Assert.Equal(bytes, File.ReadAllBytes(fixture.Output + suffix));
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static Dictionary<string, byte[]> Snapshot(string report) =>
        LeanReportTransportFixture.Suffixes.ToDictionary(suffix => suffix, suffix => File.ReadAllBytes(report + suffix));

    private static void AssertNonmaterial(Dictionary<string, byte[]> original, string report)
    {
        foreach (var (suffix, bytes) in original.Where(item => item.Key != ".materials.zip"))
            Assert.Equal(bytes, File.ReadAllBytes(report + suffix));
    }
}
