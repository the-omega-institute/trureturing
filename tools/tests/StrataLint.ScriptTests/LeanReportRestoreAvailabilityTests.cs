using Xunit.Abstractions;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class LeanReportRestoreAvailabilityTests(ITestOutputHelper output)
{
    [Fact]
    public void ProvenProvenanceMismatchStillEvictsAfterCanonicalValidation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.PrepareRestoreFaults();
        fixture.Success(fixture.MakeReport("STRATALINT_REPORT_CACHE_REMOTE=0"));
        var live = fixture.LiveSnapshot();
        fixture.SkewCachedProvenanceCoordinates();
        fixture.Success(fixture.Validate(fixture.CachedReport));

        var rejected = fixture.MakeReport("STRATALINT_REPORT_CACHE_REMOTE=0",
            "FIXTURE_RESTORE_FAILURE=provenance-mismatch", "FIXTURE_PRODUCER_EXIT=69");

        Assert.Equal(2, rejected.ExitCode);
        Assert.Contains("Error 69", rejected.Text, StringComparison.Ordinal);
        Assert.Equal(["canonical-validate=0", "private-output=clean"], fixture.RestoreEvents);
        Assert.Empty(fixture.CacheEntries);
        Assert.Equal(live, fixture.LiveSnapshot());
        Assert.Equal(2, fixture.ProducerCalls.Length);
        Assert.Empty(fixture.ReleaseCalls);
        fixture.FinishRestoreFault();
    }

    [Theory]
    [InlineData("input-evaluation")]
    [InlineData("provenance-read")]
    [InlineData("provenance-runtime")]
    [InlineData("checksum-read")]
    [InlineData("checksum-lines")]
    [InlineData("report-hash")]
    public void UnavailableRestoreCheckRetainsEveryByteForExactRecovery(string seam)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.PrepareRestoreFaults();
        fixture.Success(fixture.MakeReport("STRATALINT_REPORT_CACHE_REMOTE=0"));
        var cached = fixture.CacheSnapshot();
        var live = fixture.LiveSnapshot();
        var address = fixture.PairAddress;
        Assert.Single(fixture.ProducerCalls);

        var failed = fixture.MakeReport("STRATALINT_REPORT_CACHE_REMOTE=0",
            "FIXTURE_RESTORE_FAILURE=" + seam, "FIXTURE_PRODUCER_EXIT=69");
        fixture.FinishRestoreFault();
        var cachedReport = fixture.CachedReport;
        var members = LeanReportTransportFixture.Suffixes
            .Select(suffix => File.Exists(cachedReport + suffix)).ToArray();
        output.WriteLine("B2 seam={0}; make_exit={1}; events={2}; cached_members={3}; producers={4}",
            seam, failed.ExitCode, string.Join(",", fixture.RestoreEvents), string.Join(",", members), fixture.ProducerCalls.Length);
        Assert.Equal(2, failed.ExitCode); // make propagates the failed producer as recipe failure.
        Assert.Contains("Error 69", failed.Text, StringComparison.Ordinal);
        Assert.Equal(new[] { "canonical-validate=0", "fault=" + seam }
            .Concat(seam == "input-evaluation" ? ["input-verify=2"] : [])
            .Append("private-output=clean"), fixture.RestoreEvents);
        Assert.Equal(live, fixture.LiveSnapshot());
        Assert.Equal(2, fixture.ProducerCalls.Length);
        Assert.All(members, present => Assert.True(present, "unavailable verification evicted a cached bundle member"));
        Assert.Equal(cached, fixture.CacheSnapshot());

        var recovered = fixture.MakeReport("STRATALINT_REPORT_CACHE_REMOTE=0");
        fixture.Success(recovered);
        Assert.Contains("status=hit mode=local-exact", recovered.Text, StringComparison.Ordinal);
        Assert.Equal(address, fixture.PairAddress);
        Assert.Equal(2, fixture.ProducerCalls.Length);
        Assert.Equal(2, fixture.SlotCalls.Length);
        Assert.Equal(cached, fixture.CacheSnapshot());
        foreach (var suffix in LeanReportTransportFixture.Suffixes.Where(suffix => suffix != ".provenance.json"))
            Assert.Equal(cached[Array.IndexOf(LeanReportTransportFixture.Suffixes, suffix)],
                LeanReportTransportFixture.Digest(File.ReadAllBytes(fixture.Output + suffix)));
        Assert.Equal(["absent", "present", "present"], fixture.EnsureCalls);
        Assert.Empty(fixture.ReleaseCalls);
        output.WriteLine("B2 recovery: local-exact; producer counts=1,2,2; cache unchanged; live payload restored");
    }
}
