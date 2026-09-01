using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    [Fact]
    public void WmCreateAtomAttachesCanonicalStatusMetadata()
    {
        var raw = Encoding.UTF8.GetBytes("**title**〔closed〕");
        var atom = WmAtomizer.CreateAtom(
            raw,
            0,
            raw.Length,
            ImmutableArray<DigestionContext>.Empty);

        Assert.Equal(DigestionAtomStatusMarkerKind.Valid, atom.StatusMarker.Kind);
        Assert.Equal("closed", atom.StatusMarker.Status);
        Assert.Null(atom.StatusMarker.Qualifier);
    }

    public static TheoryData<string, byte[]> InvalidWmSources
    {
        get
        {
            var canonical = CanonicalWmFixture();
            return new TheoryData<string, byte[]>
            {
                { "missing H1", Encoding.UTF8.GetBytes(canonical.Replace(WmTitle + "\n", "BEDC-WM\n", StringComparison.Ordinal)) },
                { "missing section 7 appendix", Encoding.UTF8.GetBytes(canonical.Replace(WmAppendix, string.Empty, StringComparison.Ordinal)) },
                { "missing audit", Encoding.UTF8.GetBytes(canonical[..canonical.IndexOf("## 校核记录", StringComparison.Ordinal)]) },
                { "duplicate or out-of-order section", Encoding.UTF8.GetBytes(canonical.Replace("## 5. Section 5", "## 4. Section 5", StringComparison.Ordinal)) },
                { "unknown heading", Encoding.UTF8.GetBytes(canonical.Replace("## 6. Section 6", "## Unknown", StringComparison.Ordinal)) },
                { "leading conversation residue", Encoding.UTF8.GetBytes("可以。\n" + canonical) },
                { "missing discipline", Encoding.UTF8.GetBytes(canonical.Replace(WmDiscipline, string.Empty, StringComparison.Ordinal)) },
                { "replaced discipline", Encoding.UTF8.GetBytes(canonical.Replace("> 纪律:", "> 建议:", StringComparison.Ordinal)) },
                { "duplicate discipline", Encoding.UTF8.GetBytes(canonical.Replace(WmDiscipline, WmDiscipline + "\n" + WmDiscipline, StringComparison.Ordinal)) },
                { "audit trailing conversation LF", Encoding.UTF8.GetBytes(canonical + "可以。\n") },
                { "audit trailing conversation CRLF", Encoding.UTF8.GetBytes(canonical.ReplaceLineEndings("\r\n") + "可以。\r\n") },
                { "audit trailing conversation CR", Encoding.UTF8.GetBytes(canonical.ReplaceLineEndings("\r") + "可以。\r") },
                {
                    "audit same-line trailing sentence",
                    Encoding.UTF8.GetBytes(canonical.Replace(
                        WmCurrentTodoClosure,
                        WmCurrentTodoClosure + "可以。",
                        StringComparison.Ordinal))
                },
                {
                    "current-todo true-volume trailing conversation",
                    Encoding.UTF8.GetBytes(canonical.Replace(
                        WmCurrentTodoClosure,
                        WmCurrentTodoClosure + "这部分内容 我希望能够加入到trueturning 你觉得是否合适",
                        StringComparison.Ordinal))
                },
                { "current-todo trailing fenced conversation block", Encoding.UTF8.GetBytes(canonical + "\n```text\nassistant: 可以。\n```\n") },
                { "current-todo trailing Markdown table", Encoding.UTF8.GetBytes(canonical + "\n| role | content |\n| --- | --- |\n| assistant | 可以。 |\n") },
                {
                    "current-todo replayed closure marker",
                    Encoding.UTF8.GetBytes(canonical.Replace(
                        WmCurrentTodoClosure,
                        WmCurrentTodoClosure + "可以。" + WmCurrentTodoClosure,
                        StringComparison.Ordinal))
                },
                { "v0.2 audit trailing conversation LF", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture() + "可以。\n") },
                { "v0.2 audit trailing conversation CRLF", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().ReplaceLineEndings("\r\n") + "可以。\r\n") },
                { "v0.2 audit trailing conversation CR", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().ReplaceLineEndings("\r") + "可以。\r") },
                {
                    "v0.2 audit same-line trailing sentence",
                    Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().Replace(
                        "旧块不改。\n",
                        "旧块不改。可以。\n",
                        StringComparison.Ordinal))
                },
                { "v0.2 audit trailing fenced conversation block", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture() + "\n```text\nassistant: 可以。\n```\n") },
                { "v0.2 audit trailing Markdown table", Encoding.UTF8.GetBytes(CanonicalWmV02Fixture() + "\n| role | content |\n| --- | --- |\n| assistant | 可以。 |\n") },
                {
                    "v0.2 audit replayed closure marker",
                    Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().Replace(
                        "旧块不改。\n",
                        "旧块不改。可以。旧块不改。\n",
                        StringComparison.Ordinal))
                },
                { "non-UTF-8", [0xff, 0xfe, 0xfd] },
            };
        }
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    [InlineData("\r")]
    public void WmV1AcceptsSupportedLineEndings(string lineEnding)
    {
        var canonical = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmFixture().ReplaceLineEndings(lineEnding)),
            DigestionTestSupport.Rules);
        var evolved = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().ReplaceLineEndings(lineEnding)),
            DigestionTestSupport.Rules);

        Assert.Equal(18, canonical.Claims.Length);
        Assert.Equal(20, evolved.Claims.Length);
    }

    [Fact]
    public void PeriodicTreeV1TreatsNumberedSectionsAsAtomicClaims()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Periodic Tree\n\nProject preface.\n\n"
            + "## 0. Name and deed\n\nRoot protocol.\n\n"
            + "## 1. Mount protocol\n\nFour labels.\n\n"
            + "## 7. Construction log\n\nFirst registry.\n");

        var document = AtomizerRegistry.Atomize(AtomizerRegistry.PeriodicTreeId, bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 3);
        Assert.All(document.Claims, atom =>
            Assert.Equal(["Periodic Tree"], atom.Context.Select(static item => item.Text)));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void WmV1SplitsTheCanonicalDialectIntoExactUniqueByteAtoms()
    {
        var fixture = CanonicalWmFixtureSegments();
        var bytes = Encoding.UTF8.GetBytes(string.Concat(fixture));

        var document = AtomizerRegistry.Atomize(AtomizerRegistry.WmId, bytes, DigestionTestSupport.Rules);

        Assert.Equal(
            fixture.Select(static item => DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(item)).RawSha256),
            document.Claims.Select(static item => item.Fingerprints.RawSha256));
        Assert.Equal(GenreRegistryCheckKind.NoRegistry, document.GenreRegistryCheck.Kind);
        Assert.Equal(document.Claims.Length, document.Claims.Select(static item => item.Fingerprints.RawSha256).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(fixture.Count, document.Claims.Length);
        for (var index = 0; index < fixture.Count; index++)
        {
            Assert.Equal(Encoding.UTF8.GetBytes(fixture[index]), document.Claims[index].RawBytes.ToArray());
        }

        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void WmV1SplitIsIdempotentAndV02OnlyAddsNewVersionAndAuditAtoms()
    {
        var original = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmFixture()),
            DigestionTestSupport.Rules);
        AssertSplitIdempotent(AtomizerRegistry.WmId, original);

        var evolved = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmV02Fixture()),
            DigestionTestSupport.Rules);

        Assert.Equal(2, evolved.Claims
            .Select(static atom => atom.Fingerprints.RawSha256)
            .Except(original.Claims.Select(static atom => atom.Fingerprints.RawSha256), StringComparer.Ordinal)
            .Count());
        foreach (var atom in original.Claims)
        {
            var unchanged = Assert.Single(evolved.Claims, candidate => candidate.Fingerprints.RawSha256 == atom.Fingerprints.RawSha256);
            Assert.Equal(atom.Fingerprints, unchanged.Fingerprints);
            Assert.Equal(atom.RawBytes.ToArray(), unchanged.RawBytes.ToArray());
        }

        AssertSplitIdempotent(AtomizerRegistry.WmId, evolved);
    }

    [Theory]
    [MemberData(nameof(InvalidWmSources))]
    public void WmV1FailsClosedForStructuralDrift(string _, byte[] bytes)
    {
        var error = Record.Exception(() => AtomizerRegistry.Atomize(AtomizerRegistry.WmId, bytes, DigestionTestSupport.Rules));

        Assert.True(error is FormatException or DecoderFallbackException, error?.ToString());
    }

    [Fact]
    public void WmV1StructuralDriftStillTakesTheCoarsePath()
    {
        var bytes = Encoding.UTF8.GetBytes(
            CanonicalWmFixture().Replace(WmTitle, "BEDC-WM", StringComparison.Ordinal));
        var ledger = DigestionTestSupport.EmptyDocument(AtomizerRegistry.WmId);

        var alignment = DigestionLedgerAligner.Evaluate(
            ledger,
            DigestionTestSupport.Snapshot(("docs/source.md", bytes)),
            ledger,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(alignment.Findings);
        Assert.Contains(
            "WM source must begin with its exact H1 title",
            Assert.Single(alignment.Fallbacks).Reason,
            StringComparison.Ordinal);
        AssertContentIdentity(Assert.Single(alignment.Residual).Atom);
    }

    [Fact]
    public void WmV1AssignsEverySourceByteToAPrimaryAtom()
    {
        var bytes = Encoding.UTF8.GetBytes(CanonicalWmFixture());

        var document = AtomizerRegistry.Atomize(AtomizerRegistry.WmId, bytes, DigestionTestSupport.Rules);

        Assert.All(document.Slices, static slice => Assert.True(slice.IsClaim));
        Assert.Equal(bytes.Length, document.Slices.Sum(static slice => slice.RawBytes.Length));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void WmV1SeparatesSection7AndItsAutopsyAppendixWithNestedContext()
    {
        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmFixture()),
            DigestionTestSupport.Rules);

        var section = document.Claims.Single(static atom =>
            Encoding.UTF8.GetString(atom.RawBytes.AsSpan()).StartsWith("## 7. Section 7", StringComparison.Ordinal));
        var appendix = document.Claims.Single(static atom =>
            Encoding.UTF8.GetString(atom.RawBytes.AsSpan()).StartsWith("### §7-附", StringComparison.Ordinal));

        Assert.DoesNotContain("§7-附", Encoding.UTF8.GetString(section.RawBytes.AsSpan()), StringComparison.Ordinal);
        Assert.StartsWith("### §7-附", Encoding.UTF8.GetString(appendix.RawBytes.AsSpan()), StringComparison.Ordinal);
        Assert.Equal(
            [WmTitle[2..], "7. Section 7"],
            appendix.Context.Select(static item => item.Text));
        Assert.Equal([1, 2], appendix.Context.Select(static item => item.Level));
    }
}
