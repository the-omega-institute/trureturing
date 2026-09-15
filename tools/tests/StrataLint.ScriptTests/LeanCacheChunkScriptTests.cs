using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed class LeanCacheChunkScriptTests
{
    [Theory]
    [InlineData(-1)]
    [InlineData(0)]
    [InlineData(1)]
    public void SmallArchivePublishesAndFetchesAsOneAsset(int thresholdOffset)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture("01234567");

        fixture.AssertSuccess(fixture.Publish(thresholdOffset < 0 ? null : fixture.ArchiveBytes.Length + thresholdOffset));

        Assert.Equal(new[] { "lean-build.tgz", "manifest.json" }, fixture.Assets(fixture.Tag));
        Assert.Single(fixture.Manifest(fixture.Tag)["parts"]!.AsArray());
        Assert.Equal(fixture.ArchiveBytes, fixture.ReadAsset(fixture.Tag, "lean-build.tgz"));
        fixture.AssertSuccess(fixture.Fetch());
        Assert.Equal("01234567", fixture.Unpacked);
        Assert.Equal("report-seed", fixture.UnpackedReport);
        Assert.Equal(new[] { "manifest.json", "lean-build.tgz" }, fixture.DownloadPatterns);
    }

    [Theory]
    [InlineData("1")]
    [InlineData("8")]
    public void PublishingIgnoresChunkSizeEnvironment(string chunkEnvironment)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();

        fixture.AssertSuccess(fixture.Publish(chunkEnvironment: chunkEnvironment));

        Assert.Equal(new[] { "lean-build.tgz", "manifest.json" }, fixture.Assets(fixture.Tag));
        Assert.Single(fixture.Manifest(fixture.Tag)["parts"]!.AsArray());
    }

    [Fact]
    public void ArchiveExceedingSuffixCapacityFailsBeforePublishing()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();

        var result = fixture.Publish(1);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("\"status\":\"failed\"", result.Text, StringComparison.Ordinal);
        Assert.Contains("100 parts", result.Text, StringComparison.Ordinal);
        Assert.False(fixture.HasRelease);
        Assert.Empty(fixture.GhCalls);
    }

    [Fact]
    public void ThreePartPublishFetchRoundTripPreservesBytesAndDigests()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        var chunkBytes = (fixture.ArchiveBytes.Length + 2) / 3;

        fixture.AssertSuccess(fixture.Publish(chunkBytes));

        var names = new[] { "lean-build.tgz.part-00", "lean-build.tgz.part-01", "lean-build.tgz.part-02" };
        Assert.Equal([.. names, "manifest.json"], fixture.Assets(fixture.Tag));
        var manifest = fixture.Manifest(fixture.Tag);
        Assert.Equal("lean-release-seed-v3", manifest["schema"]!.GetValue<string>());
        Assert.Equal(3, manifest["parts"]!.AsArray().Count);
        for (var i = 0; i < names.Length; i++)
        {
            var bytes = fixture.ArchiveBytes.Skip(i * chunkBytes).Take(chunkBytes).ToArray();
            var part = manifest["parts"]![i]!;
            Assert.Equal(names[i], part["name"]!.GetValue<string>());
            Assert.Equal(bytes, fixture.ReadAsset(fixture.Tag, names[i]));
            Assert.Equal(LeanCacheChunkFixture.Digest(bytes), part["sha256"]!.GetValue<string>());
            Assert.Equal(bytes.Length, part["bytes"]!.GetValue<int>());
        }
        Assert.Equal(LeanCacheChunkFixture.Digest(fixture.ArchiveBytes), manifest["archive_sha256"]!.GetValue<string>());
        Assert.Equal(fixture.ArchiveBytes.Length, manifest["archive_bytes"]!.GetValue<int>());
        var create = Assert.Single(fixture.GhCalls, args => args[1] == "create");
        Assert.Equal(LeanCacheChunkFixture.ProducerSha, create[Array.IndexOf(create, "--target") + 1]);
        Assert.Equal(LeanCacheChunkFixture.ProducerSha, manifest["producer_commit_sha"]!.GetValue<string>());
        Assert.Equal("4242", manifest["workflow_run_id"]!.GetValue<string>());
        Assert.Equal("1", manifest["workflow_run_attempt"]!.GetValue<string>());

        fixture.AssertSuccess(fixture.Fetch());

        Assert.Equal(LeanCacheChunkFixture.Archive, fixture.Unpacked);
        Assert.Equal("report-seed", fixture.UnpackedReport);
        Assert.Equal(["manifest.json", .. names], fixture.DownloadPatterns);
    }

    [Fact]
    public void PartNamesRemainInByteOrderBeyondNineParts()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        var chunkBytes = (fixture.ArchiveBytes.Length + 10) / 11;

        fixture.AssertSuccess(fixture.Publish(chunkBytes));

        Assert.Equal(11, fixture.Manifest(fixture.Tag)["parts"]!.AsArray().Count);
        Assert.Equal(fixture.ArchiveBytes.Skip(10 * chunkBytes), fixture.ReadAsset(fixture.Tag, "lean-build.tgz.part-10"));
        fixture.AssertSuccess(fixture.Fetch());
        Assert.Equal(LeanCacheChunkFixture.Archive, fixture.Unpacked);
    }

    [Theory]
    [InlineData("missing-part", "asset set")]
    [InlineData("bad-part", "part checksum or size mismatch")]
    [InlineData("missing-part-digest", "invalid archive parts")]
    [InlineData("bad-whole", "archive checksum or size mismatch")]
    [InlineData("bad-part-size", "archive byte count")]
    [InlineData("bad-whole-size", "archive byte count")]
    [InlineData("invalid-parts", "invalid archive parts")]
    [InlineData("empty-parts", "invalid archive parts")]
    [InlineData("missing-parts", "invalid archive parts")]
    [InlineData("old-schema", "snapshot partition or source attribution mismatch")]
    public void CorruptChunkedCandidateFailsClosed(string deviation, string reason)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        fixture.AddRelease(fixture.Tag, deviation: deviation);

        var result = fixture.Fetch();

        AssertMiss(result, reason);
        Assert.Null(fixture.Unpacked);
        Assert.Null(fixture.UnpackedReport);
    }

    [Theory]
    [InlineData("bad-github-part-digest", "transferred asset digest mismatch")]
    [InlineData("bad-github-manifest-digest", "transferred asset digest mismatch")]
    [InlineData("extra-asset", "asset set")]
    [InlineData("no-producer", "snapshot partition or source attribution mismatch")]
    [InlineData("no-run-id", "snapshot partition or source attribution mismatch")]
    [InlineData("no-attempt", "snapshot partition or source attribution mismatch")]
    [InlineData("wrong-target", "snapshot partition or source attribution mismatch")]
    [InlineData("wrong-partition", "snapshot partition or source attribution mismatch")]
    public void ChunkedReleaseRetainsDigestInventoryAndAttributionChecks(string deviation, string reason)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        fixture.AddRelease(fixture.Tag, deviation: deviation);

        var result = fixture.Fetch();

        AssertMiss(result, reason);
        Assert.Null(fixture.Unpacked);
        Assert.Null(fixture.UnpackedReport);
    }

    [Theory]
    [InlineData("missing-part", false)]
    [InlineData("bad-part", false)]
    [InlineData("bad-whole", false)]
    [InlineData("missing-part", true)]
    [InlineData("bad-part", true)]
    [InlineData("bad-whole", true)]
    [InlineData("download-failure", true)]
    [InlineData("draft", true)]
    public void FetchContinuesToNextSamePartitionCandidate(string deviation, bool multipartFallback)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        var valid = fixture.CandidateTag(4241);
        fixture.AddRelease(fixture.Tag, deviation: deviation);
        fixture.AddRelease(valid, chunked: multipartFallback);
        fixture.ListReleases(fixture.Tag, valid);

        var result = fixture.Fetch();

        fixture.AssertSuccess(result);
        if (deviation != "draft") Assert.Contains("\"status\":\"miss\"", result.Text, StringComparison.Ordinal);
        Assert.Contains($"\"resolved\":\"{valid}\"", result.Text, StringComparison.Ordinal);
        Assert.Contains("\"mode\":\"partition\"", result.Text, StringComparison.Ordinal);
        Assert.Contains("\"workflow_run_id\":\"4241\"", result.Text, StringComparison.Ordinal);
        Assert.Contains($"\"producer_commit_sha\":\"{LeanCacheChunkFixture.ProducerSha}\"", result.Text, StringComparison.Ordinal);
        Assert.Equal(LeanCacheChunkFixture.Archive, fixture.Unpacked);
        Assert.Equal("report-seed", fixture.UnpackedReport);
        Assert.DoesNotContain(fixture.Tag, fixture.DownloadTags.TakeLast(2));
    }

    [Theory]
    [InlineData("mathlib")]
    [InlineData("os")]
    [InlineData("arch")]
    public void FetchSelectsOnlyTheSameResolvedPartition(string mismatch)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        var partition = mismatch switch
        {
            "mathlib" => "f" + fixture.Partition[1..],
            "os" => fixture.Partition[..41] + "otheros-" + fixture.Partition.Split('-')[^1],
            _ => fixture.Partition[..fixture.Partition.LastIndexOf('-')] + "-otherarch",
        };
        var other = fixture.CandidateTag(4243, partition);
        fixture.AddRelease(other, partition: partition);

        AssertMiss(fixture.Fetch(allowSeed: true), "no published snapshot in this partition");
        Assert.Null(fixture.Unpacked);
        Assert.Null(fixture.UnpackedReport);
        Assert.DoesNotContain(other, fixture.DownloadTags);

        fixture.AddRelease(fixture.Tag);
        fixture.ListReleases(other, fixture.Tag);
        fixture.AssertSuccess(fixture.Fetch());
        Assert.Equal(LeanCacheChunkFixture.Archive, fixture.Unpacked);
        Assert.DoesNotContain(other, fixture.DownloadTags);
    }

    [Theory]
    [InlineData(null, "4242")]
    [InlineData("nothex", "4242")]
    [InlineData(LeanCacheChunkFixture.ProducerSha, "")]
    public void PublishRefusesUnattributedSnapshotsAfterBuilding(string? commit, string runId)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();

        var result = fixture.Publish(commit: commit, runId: runId);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("\"status\":\"failed\"", result.Text, StringComparison.Ordinal);
        Assert.Contains("requires commit, run ID and attempt attribution", result.Text, StringComparison.Ordinal);
        Assert.False(fixture.HasRelease);
        Assert.Equal(new[] { "lean" }, fixture.BuildRuns);
    }

    [Fact]
    public void FailedMultipartUploadCannotBeFetched()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();

        var result = fixture.Publish((fixture.ArchiveBytes.Length + 2) / 3, failure: "upload");

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("\"status\":\"failed\"", result.Text, StringComparison.Ordinal);
        Assert.True(fixture.Metadata(fixture.Tag)["draft"]!.GetValue<bool>());
        Assert.Single(fixture.Assets(fixture.Tag));
        AssertMiss(fixture.Fetch(), "no published snapshot in this partition");
        Assert.Null(fixture.Unpacked);
        Assert.Null(fixture.UnpackedReport);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ConcurrentMultipartPublishersNeverClobberSnapshots(bool sameRun)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        fixture.SetChunkBytes((fixture.ArchiveBytes.Length + 2) / 3);
        var otherRun = sameRun ? 4242 : 4243;

        var results = await Task.WhenAll(Task.Run(() => fixture.Publish()),
            Task.Run(() => fixture.Publish(run: otherRun)));

        Assert.All(results, fixture.AssertSuccess);
        Assert.Equal(sameRun ? 1 : 2, results.Count(result => result.Text.Contains("\"status\":\"published\"", StringComparison.Ordinal)));
        Assert.Equal(sameRun ? 1 : 0, results.Count(result => result.Text.Contains("\"status\":\"failed\"", StringComparison.Ordinal)));
        foreach (var tag in new[] { fixture.Tag, fixture.CandidateTag(otherRun) }.Distinct())
        {
            Assert.False(fixture.Metadata(tag)["draft"]!.GetValue<bool>());
            Assert.Equal(4, fixture.Assets(tag).Length);
            Assert.Equal(3, fixture.Manifest(tag)["parts"]!.AsArray().Count);
        }
        fixture.AssertSuccess(fixture.Fetch());
        Assert.Equal(LeanCacheChunkFixture.Archive, fixture.Unpacked);
        Assert.Equal("report-seed", fixture.UnpackedReport);
    }

    private static void AssertMiss(LeanCacheChunkFixture.Attempt result, string reason)
    {
        Assert.Equal(1, result.ExitCode);
        var line = result.Text.Split('\n').Last(value => value.StartsWith("LEAN_CACHE_FETCH ", StringComparison.Ordinal));
        var receipt = JsonNode.Parse(line["LEAN_CACHE_FETCH ".Length..])!;
        Assert.Equal("miss", receipt["status"]!.GetValue<string>());
        Assert.Contains(reason, receipt["reason"]!.GetValue<string>(), StringComparison.Ordinal);
    }
}
