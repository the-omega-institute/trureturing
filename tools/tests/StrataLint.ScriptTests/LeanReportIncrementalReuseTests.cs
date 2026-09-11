using System.Text.Json;
using Xunit.Abstractions;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class LeanReportIncrementalReuseTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData("valid")]
    [InlineData("invalid-archive")]
    [InlineData("missing-member")]
    public void AuxiliarySourceDeltaReusesOnlyACompleteBaseline(string damage)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.UseRealInspector();
        var before = fixture.ReadInspectorInputs();
        fixture.Success(fixture.MakeInspectedReport());
        Assert.Single(fixture.ProducerCalls);
        var baseline = Path.Combine(fixture.CacheRoot, before.Pair, "raw-lean-report.json");
        fixture.Success(fixture.Validate(baseline));
        var original = LeanReportTransportFixture.Suffixes.ToDictionary(suffix => suffix, suffix => File.ReadAllBytes(baseline + suffix));
        using (var report = JsonDocument.Parse(original[""]))
            Assert.All(report.RootElement.GetProperty("modules").EnumerateArray(),
                module => Assert.NotEmpty(module.GetProperty("declarations").EnumerateArray()));

        var auxiliary = Path.Combine(fixture.Repository, LeanReportTransportFixture.AuxiliarySource);
        fixture.WriteSource(LeanReportTransportFixture.AuxiliarySource, File.ReadAllText(auxiliary) + "-- comment-only delta\n");
        var after = fixture.ReadInspectorInputs();
        Assert.Equal(before.Producer, after.Producer);
        Assert.Equal(before.Resident, after.Resident);
        Assert.Equal(before.Config, after.Config);
        Assert.NotEqual(before.Sources, after.Sources);
        Assert.NotEqual(before.Repository, after.Repository);
        Assert.NotEqual(before.Pair, after.Pair);
        Assert.Equal(new[] { "D5.Probe\tD5/Probe.lean", "Trureturing\tTrureturing.lean" }, before.Modules);
        Assert.Equal(before.Modules, after.Modules);
        Assert.Equal(before.Hashes, after.Hashes);
        var current = Path.Combine(fixture.CacheRoot, after.Pair, "raw-lean-report.json");
        Assert.Equal(new[] { baseline }, fixture.CacheEntries);
        Assert.False(File.Exists(current));
        var stale = fixture.Input("verify", "--repository", fixture.Repository, "--report", baseline);
        Assert.Equal(2, stale.ExitCode);
        Assert.Contains("raw Lean report is stale for current repository inputs", stale.Text, StringComparison.Ordinal);

        if (damage != "valid")
        {
            // Damage only the old material archive, keeping every report and
            // attestation byte intact. The missing-member ZIP remains readable.
            if (damage == "invalid-archive") File.WriteAllText(baseline + ".materials.zip", "not a material ZIP");
            else
            {
                using var stream = new MemoryStream();
                using (var zip = new System.IO.Compression.ZipArchive(stream, System.IO.Compression.ZipArchiveMode.Create, true)) { }
                File.WriteAllBytes(baseline + ".materials.zip", stream.ToArray());
            }
            var rejected = fixture.Validate(baseline);
            Assert.Equal(1, rejected.ExitCode);
            Assert.Contains(damage == "invalid-archive" ? "File is not a zip file" : "material-members-mismatch",
                rejected.Text, StringComparison.Ordinal);
        }
        foreach (var (suffix, bytes) in original.Where(item => item.Key != ".materials.zip"))
            Assert.Equal(bytes, File.ReadAllBytes(baseline + suffix));
        var injected = File.ReadAllBytes(baseline + ".materials.zip");

        var result = fixture.MakeInspectedReport();
        fixture.Success(result);
        Assert.Contains("LEAN_REPORT_DELTA_PLAN mode=reuse changed=0 added=0 removed=0 recheck=0", result.Text, StringComparison.Ordinal);
        var liveValidation = fixture.Validate(fixture.Output);
        var cacheValidation = fixture.Validate(current);
        var liveInput = fixture.Input("verify", "--repository", fixture.Repository, "--report", fixture.Output);
        var cacheInput = fixture.Input("verify", "--repository", fixture.Repository, "--report", current);
        output.WriteLine("A1 scenario={0} {1}; make_exit={2}; extraction_calls={3}; live_validate={4}; cache_validate={5}; live_verify={6}; cache_verify={7}; baseline_material_copied={8}",
            damage, result.Stdout.Split('\n').Single(line => line.StartsWith("LEAN_REPORT_DELTA mode=", StringComparison.Ordinal)),
            result.ExitCode, fixture.ProducerCalls.Length - 1, liveValidation.ExitCode, cacheValidation.ExitCode,
            liveInput.ExitCode, cacheInput.ExitCode, injected.SequenceEqual(File.ReadAllBytes(fixture.Output + ".materials.zip")));
        output.WriteLine("A1 coordinates before={0} after={1}", JsonSerializer.Serialize(before), JsonSerializer.Serialize(after));

        Assert.Contains("LEAN_REPORT_DELTA mode=" + (damage == "valid" ? "reuse" : "full-fallback"), result.Text, StringComparison.Ordinal);
        Assert.Equal(damage == "valid" ? 1 : 2, fixture.ProducerCalls.Length);
        if (damage != "valid") Assert.Contains("cached reuse bundle rejected", result.Text, StringComparison.Ordinal);
        fixture.Success(liveValidation);
        fixture.Success(cacheValidation);
        fixture.Success(liveInput);
        fixture.Success(cacheInput);
        Assert.Equal(original[""], File.ReadAllBytes(fixture.Output));
        Assert.Equal(original[".materials.zip"], File.ReadAllBytes(fixture.Output + ".materials.zip"));
        Assert.Equal(original[""], File.ReadAllBytes(current));
        Assert.Equal(original[".materials.zip"], File.ReadAllBytes(current + ".materials.zip"));
        foreach (var (suffix, bytes) in original.Where(item => item.Key != ".materials.zip"))
            Assert.Equal(bytes, File.ReadAllBytes(baseline + suffix));
        Assert.Equal(injected, File.ReadAllBytes(baseline + ".materials.zip"));
        Assert.Empty(fixture.ReleaseCalls);
    }
}
