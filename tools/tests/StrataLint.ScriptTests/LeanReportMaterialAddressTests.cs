using System.Text.Json;
using Xunit.Abstractions;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class LeanReportMaterialAddressTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData("exact", false)]
    [InlineData("exact", true)]
    [InlineData("reuse", false)]
    [InlineData("reuse", true)]
    [InlineData("delta", false)]
    [InlineData("delta", true)]
    public void CacheReuseRequiresAddressConsistentSelectedMaterial(string mode, bool tampered)
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
            var source = mode == "reuse" ? LeanReportTransportFixture.AuxiliarySource : "Trureturing.lean";
            fixture.WriteSource(source, File.ReadAllText(Path.Combine(fixture.Repository, source)) + "-- source delta\n");
        }
        var after = fixture.ReadInspectorInputs();
        Assert.Equal(before.Producer, after.Producer);
        Assert.Equal(before.Resident, after.Resident);
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
            Assert.Equal(2, fixture.Input("verify", "--repository", fixture.Repository, "--report", baseline).ExitCode);
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
        var copied = injected.SequenceEqual(File.ReadAllBytes(fixture.Output + ".materials.zip"));
        output.WriteLine("P1 mode={0} tampered={1}; baseline_validate={2}; make_exit={3}; extractions={4}; copied_injected={5}; live/cache_validate={6}/{7}; live/cache_input={8}/{9}; final={10}",
            mode, tampered, validation.ExitCode, result.ExitCode, JsonSerializer.Serialize(fixture.ExtractedModules),
            copied, liveValidation.ExitCode, cacheValidation.ExitCode, liveInput.ExitCode, cacheInput.ExitCode,
            string.Join(" | ", result.Text.Split('\n').Where(line => line.StartsWith("LEAN_REPORT_DELTA", StringComparison.Ordinal)
                || line.Contains("mode=local-exact", StringComparison.Ordinal))));
        if (mode != "exact")
        {
            AssertNonmaterial(original, baseline);
            Assert.Equal(injected, File.ReadAllBytes(baseline + ".materials.zip"));
            var counts = mode == "reuse" ? "changed=0 added=0 removed=0 recheck=0" : "changed=1 added=0 removed=0 recheck=1";
            Assert.Contains($"LEAN_REPORT_DELTA_PLAN mode={mode} {counts}", result.Text, StringComparison.Ordinal);
            Assert.Contains($"LEAN_REPORT_DELTA mode={(tampered ? "full-fallback" : mode)} {counts}", result.Text, StringComparison.Ordinal);
        }
        else Assert.Contains(tampered ? "status=miss reason=local-entry-unavailable" : "status=hit mode=local-exact",
            result.Text, StringComparison.Ordinal);
        Assert.Equal(tampered ? 1 : 0, validation.ExitCode);
        if (tampered) Assert.Contains("statement material address mismatch", validation.Text, StringComparison.Ordinal);
        var expectedExtractions = 1 + (mode == "delta" ? 1 : 0) + (tampered ? 1 : 0);
        Assert.Equal(expectedExtractions, fixture.ProducerCalls.Length);
        Assert.Equal(expectedExtractions, fixture.ExtractedModules.Length);
        if (mode == "delta") Assert.Equal(new[] { "Trureturing" }, fixture.ExtractedModules[1]);
        if (tampered) Assert.Equal(new[] { "D5.Probe", "Trureturing" }, fixture.ExtractedModules[^1].Order(StringComparer.Ordinal));
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
