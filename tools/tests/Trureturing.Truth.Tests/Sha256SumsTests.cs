using System;
using System.Collections.Generic;
using System.Text;
using Trureturing.Truth;
using Xunit;

namespace Trureturing.Truth.Tests;

public sealed class Sha256SumsTests
{
    // Standard, hand-verifiable SHA-256 vectors — independent of the implementation under test.
    private const string HexAbc = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
    private const string HexEmpty = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";

    [Fact]
    public void HashHexMatchesKnownSha256Vectors()
    {
        Assert.Equal(HexAbc, Sha256Sums.HashHex(Encoding.UTF8.GetBytes("abc")));
        Assert.Equal(HexEmpty, Sha256Sums.HashHex(ReadOnlySpan<byte>.Empty));
    }

    [Fact]
    public void FormatSortsByNameWithTwoSpacesAndTrailingNewline()
    {
        // Entries deliberately reversed to prove the writer sorts by filename (Ordinal), and to
        // pin the exact wire shape: "<hex>  <name>" (two spaces), lines joined by "\n", trailing "\n".
        var entries = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["b.json"] = HexEmpty,
            ["a.json"] = HexAbc,
        };

        var expected = HexAbc + "  a.json\n" + HexEmpty + "  b.json\n";
        Assert.Equal(expected, Sha256Sums.Format(entries));
    }

    [Fact]
    public void ReleaseDigestMatchesIndependentShasumGolden()
    {
        // SHA256SUMS text for the bundle {a.json="abc", b.json=""}. The expected release digest was
        // computed by an INDEPENDENT tool (`shasum -a 256`), NOT by this library, so a shared
        // canonicalization mistake cannot make a producer and a verifier agree on the same wrong
        // value (the bootstrap-oracle circularity an adversarial review flagged).
        var sums = HexAbc + "  a.json\n" + HexEmpty + "  b.json\n";

        Assert.Equal(
            "sha256:2d097763a5dbd7c002e835714ab586464c01647822a7f19b6528ab26993b715d",
            Sha256Sums.ReleaseDigest(sums));
    }

    [Fact]
    public void ReleaseDigestOverBytesIsByteFaithfulForMalformedUtf8()
    {
        // 0xFF and 0xFE are both invalid UTF-8 and decode to the SAME replacement character, so a
        // digest taken over a decoded-then-re-encoded string would collapse them to one value. The
        // byte overload a verifier must use hashes the raw bytes and keeps them distinct.
        Assert.NotEqual(
            Sha256Sums.ReleaseDigest(new byte[] { 0xFF }),
            Sha256Sums.ReleaseDigest(new byte[] { 0xFE }));
    }
}
