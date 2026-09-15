using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Tests;

public sealed class LeanCacheChunkScriptTests
{
    [Theory]
    [InlineData("default")]
    [InlineData("8")]
    [InlineData("9")]
    public void SmallArchivePublishesAndFetchesAsOneAsset(string chunkBytes)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture("01234567");

        fixture.AssertSuccess(fixture.Publish(chunkBytes));

        Assert.Equal(new[] { "lean-build.tgz", "manifest.txt" }, fixture.Assets(fixture.Tag));
        Assert.Contains("parts=1\n", fixture.Manifest(fixture.Tag), StringComparison.Ordinal);
        fixture.AssertSuccess(fixture.Fetch());
        Assert.Equal("01234567", fixture.Unpacked);
        Assert.Equal(new[] { "manifest.txt", "lean-build.tgz" }, fixture.DownloadPatterns);
    }

    [Theory]
    [InlineData("1")]
    [InlineData("8")]
    public void PublishingIgnoresChunkSizeEnvironment(string chunkEnvironment)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture(new string('a', 102));

        fixture.AssertSuccess(fixture.Publish("default", chunkEnvironment));

        Assert.Equal(new[] { "lean-build.tgz", "manifest.txt" }, fixture.Assets(fixture.Tag));
        Assert.Contains("parts=1\n", fixture.Manifest(fixture.Tag), StringComparison.Ordinal);
    }

    [Fact]
    public void ArchiveExceedingSuffixCapacityFailsBeforePublishing()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture(new string('a', 101));

        var result = fixture.Publish("1");

        Assert.NotEqual(0, result.ExitCode);
        Assert.False(fixture.HasRelease);
    }

    [Fact]
    public void ThreePartPublishFetchRoundTripPreservesBytesAndDigests()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture("0123456789abcdefgh");

        fixture.AssertSuccess(fixture.Publish("8"));

        Assert.Equal(new[] { "lean-build.tgz.part-00", "lean-build.tgz.part-01", "lean-build.tgz.part-02", "manifest.txt" }, fixture.Assets(fixture.Tag));
        var manifest = fixture.Manifest(fixture.Tag);
        Assert.Contains("parts=3\n", manifest, StringComparison.Ordinal);
        foreach (var (index, bytes) in new[] { (0, "01234567"), (1, "89abcdef"), (2, "gh") })
        {
            Assert.Equal(bytes, fixture.ReadAsset(fixture.Tag, $"lean-build.tgz.part-{index:D2}"));
            Assert.Contains($"part_sha256_{index}={Digest(bytes)}\n", manifest, StringComparison.Ordinal);
        }
        Assert.Contains($"archive_sha256={Digest("0123456789abcdefgh")}\n", manifest, StringComparison.Ordinal);
        fixture.AssertSuccess(fixture.Fetch());
        Assert.Equal("0123456789abcdefgh", fixture.Unpacked);
        Assert.Equal(new[] { "manifest.txt", "lean-build.tgz.part-*" }, fixture.DownloadPatterns);
    }

    [Fact]
    public void PartNamesRemainInByteOrderBeyondNineParts()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture("0123456789a");

        fixture.AssertSuccess(fixture.Publish("1"));
        Assert.Contains("parts=11\n", fixture.Manifest(fixture.Tag), StringComparison.Ordinal);
        Assert.Equal("a", fixture.ReadAsset(fixture.Tag, "lean-build.tgz.part-10"));
        fixture.AssertSuccess(fixture.Fetch());
        Assert.Equal("0123456789a", fixture.Unpacked);
    }

    [Fact]
    public void FetchReadsOldSingleAssetReleaseWithoutPartsField()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        var legacyTag = fixture.CandidateTag('4', '3');
        fixture.AddRelease(legacyTag, chunked: false, oldManifest: true);
        fixture.ListReleases(legacyTag);

        fixture.AssertSuccess(fixture.Fetch());

        Assert.Equal(LeanCacheChunkFixture.Archive, fixture.Unpacked);
        Assert.Equal(new[] { "manifest.txt", "lean-build.tgz" }, fixture.DownloadPatterns.TakeLast(2));
    }

    [Theory]
    [InlineData("missing-part", "missing part")]
    [InlineData("bad-part", "part checksum mismatch")]
    [InlineData("missing-part-digest", "part checksum mismatch")]
    [InlineData("bad-whole", "digest mismatch")]
    [InlineData("invalid-parts", "invalid parts count")]
    [InlineData("empty-parts", "invalid parts count")]
    [InlineData("missing-snapshot", "manifest addresses do not match release tag")]
    [InlineData("malformed-snapshot", "malformed snapshot address")]
    [InlineData("stale-snapshot", "exact snapshot address mismatch")]
    [InlineData("stale-sources", "exact snapshot address mismatch")]
    public void CorruptChunkedCandidateFailsClosed(string deviation, string reason)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        fixture.AddRelease(fixture.Tag, deviation: deviation);

        var result = fixture.Fetch();

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("\"status\":\"miss\"", result.Text, StringComparison.Ordinal);
        Assert.Contains(reason, result.Text.Split('\n').Last(line => line.StartsWith("LEAN_CACHE_FETCH ", StringComparison.Ordinal)), StringComparison.Ordinal);
        Assert.Null(fixture.Unpacked);
    }

    [Theory]
    [InlineData("bad-github-part-digest", "do not match the digest GitHub recorded")]
    [InlineData("extra-asset", "assets, expected exactly 4")]
    public void ChunkedReleaseRetainsGithubDigestAndInventoryChecks(string deviation, string reason)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        fixture.AddRelease(fixture.Tag, deviation: deviation);

        var result = fixture.Fetch();

        Assert.Equal(1, result.ExitCode);
        Assert.Contains(reason, result.Text.Split('\n').Last(line => line.StartsWith("LEAN_CACHE_FETCH ", StringComparison.Ordinal)), StringComparison.Ordinal);
        Assert.Null(fixture.Unpacked);
    }

    [Theory]
    [InlineData("exact", "missing-part")]
    [InlineData("exact", "bad-part")]
    [InlineData("exact", "bad-whole")]
    [InlineData("prefix", "missing-part")]
    [InlineData("prefix", "bad-part")]
    [InlineData("prefix", "bad-whole")]
    [InlineData("seed", "missing-part")]
    [InlineData("seed", "bad-part")]
    [InlineData("seed", "bad-whole")]
    public void FetchContinuesToNextCandidateAfterCorruption(string mode, string deviation)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        var config = mode == "seed" ? '5' : '4';
        var corrupt = mode == "exact" ? fixture.Tag : fixture.CandidateTag(config, 'a');
        var valid = fixture.CandidateTag(config, 'b');
        fixture.AddRelease(corrupt, deviation: deviation);
        fixture.AddRelease(valid, chunked: false);
        fixture.ListReleases(corrupt, valid);

        var result = fixture.Fetch(allowSeed: mode == "seed");

        fixture.AssertSuccess(result);
        Assert.Contains("\"status\":\"miss\"", result.Text, StringComparison.Ordinal);
        Assert.Contains($"\"resolved\":\"{valid}\"", result.Text, StringComparison.Ordinal);
        Assert.Contains($"\"mode\":\"{(mode == "exact" ? "prefix" : mode)}\"", result.Text, StringComparison.Ordinal);
        Assert.Equal(LeanCacheChunkFixture.Archive, fixture.Unpacked);
    }

    [Fact]
    public void PrefixCandidatesTakePriorityOverNewerSeeds()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        var seed = fixture.CandidateTag('5', 'a');
        var prefix = fixture.CandidateTag('4', 'b');
        fixture.AddRelease(seed);
        fixture.AddRelease(prefix);
        fixture.ListReleases(seed, prefix);

        var result = fixture.Fetch(allowSeed: true);

        fixture.AssertSuccess(result);
        Assert.Contains($"\"resolved\":\"{prefix}\"", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain(seed, fixture.DownloadTags);
    }

    [Fact]
    public void SeedRequiresExplicitOptIn()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanCacheChunkFixture();
        var seed = fixture.CandidateTag('5', 'a');
        fixture.AddRelease(seed);
        fixture.ListReleases(seed);

        Assert.Equal(1, fixture.Fetch().ExitCode);
        Assert.Null(fixture.Unpacked);
        Assert.DoesNotContain(seed, fixture.DownloadTags);
    }

    private static string Digest(string value) => Convert.ToHexStringLower(SHA256.HashData(Encoding.ASCII.GetBytes(value)));
}
