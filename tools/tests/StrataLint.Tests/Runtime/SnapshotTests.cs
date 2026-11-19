using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class SnapshotTests
{
    private const string Header = "/- GID: D5/S0/Carrier/Ring\n"
        + "   generality: G\n"
        + "   mirror-B: D5/B/S0/Carrier/Ring\n"
        + "   mirror-E: none(waiver:pure-definition)\n"
        + "   anchors: []\n"
        + "   digest: header text -/\n";

    public static IEnumerable<object[]> HeaderCases()
    {
        var utility = Header.Replace("   digest:", "   utility: refutation(claim,result)\n   digest:", StringComparison.Ordinal);
        foreach (var header in new[] { Header, utility })
        {
            yield return [header, true];
            yield return [header.TrimEnd('\n'), true];
            yield return [header + "def body := 0\n-- body -/\n\n\n\n\n\n", true];
            yield return [header.TrimEnd('\n') + " suffix -/ trailing\nbody\n", true];
            yield return [header.Replace("header text", "中文 é 🚀 -/ greedy", StringComparison.Ordinal), true];
            yield return [header.Replace("Carrier/Ring", "载体/🚀", StringComparison.Ordinal)
                .Replace("anchors: []", "anchors: [α, 🚀]", StringComparison.Ordinal), true];
            yield return [header.Replace("header text", new string('界', 128 * 1024) + "🚀", StringComparison.Ordinal), true];
            yield return [header.Replace("Carrier/Ring", new string('x', 128 * 1024), StringComparison.Ordinal), true];
            yield return ["\uFEFF" + header, false];
            yield return [header.Replace("\n", "\r\n", StringComparison.Ordinal), false];
            yield return [header.TrimEnd('\n') + "\r\nbody\n", true];
            yield return [header.Replace("header text", " \t", StringComparison.Ordinal), false];
            yield return [header.Replace("header text", "wrapped\ndigest", StringComparison.Ordinal), false];
            yield return [header.Replace("generality: G", "generality: X", StringComparison.Ordinal), false];
            yield return [header.Replace("anchors: []", "anchors: [\n]", StringComparison.Ordinal), false];
            yield return [header.Replace("anchors: []", "anchors: [α, " + new string('x', 128 * 1024) + ", 🚀]", StringComparison.Ordinal), true];
            yield return [header.Replace(" -/", "", StringComparison.Ordinal) + "\n -/\n", false];
        }
        yield return [utility.Replace("refutation(claim,result)", "中文 🚀", StringComparison.Ordinal), true];
        yield return [utility.Replace("refutation(claim,result)", "", StringComparison.Ordinal), true];
        yield return [utility.Replace("refutation(claim,result)", new string('x', 128 * 1024), StringComparison.Ordinal), true];
        yield return [utility.Replace("refutation(claim,result)", "wrapped\nutility", StringComparison.Ordinal), false];
        yield return ["", false];
        yield return ["/- GID: incomplete", false];
    }

    [Theory]
    [MemberData(nameof(HeaderCases))]
    public void FileHeaderParserMatchesCanonicalStringParser(string source, bool accepted)
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(RuleFixture.RingPath, source)]))).Snapshot;
        var file = Assert.Single(snapshot.Files).Value;

        Assert.Equal(accepted, RepositoryRules.TryHeader(source, out var expected));
        Assert.Equal(accepted, RepositoryRules.TryHeader(file, out var actual));
        Assert.Equal(expected.Gid, actual.Gid);
        Assert.Equal(expected.Generality, actual.Generality);
        Assert.Equal(expected.MirrorB, actual.MirrorB);
        Assert.Equal(expected.MirrorE, actual.MirrorE);
        Assert.Equal(expected.Anchors, actual.Anchors);
        Assert.Equal(expected.Utility, actual.Utility);
        Assert.Equal(expected.BodyOffset, actual.BodyOffset);
        Assert.Equal(file.Text[expected.BodyOffset..], source[actual.BodyOffset..]);
    }

    [Fact]
    public void FileHeaderBodyOffsetCountsUtf16AndIncludesGreedyDigestSuffix()
    {
        var prefix = Header.TrimEnd('\n').Replace("header text", "é🚀 -/ still digest", StringComparison.Ordinal)
            + " more -/\n";
        var file = Assert.Single(Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(RuleFixture.RingPath, prefix + "body\n")]))).Snapshot.Files).Value;

        Assert.True(RepositoryRules.TryHeader(file, out var header));
        Assert.Equal(prefix.Length, header.BodyOffset);
        Assert.NotEqual(Encoding.UTF8.GetByteCount(prefix), header.BodyOffset);
        Assert.Equal("body\n", file.Text[header.BodyOffset..]);
    }

    [Fact]
    public void FileHeaderParserPreservesOpaqueAndExplicitTextSemantics()
    {
        var path = RepoPath.CreateKnown(RuleFixture.RingPath);
        var bytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(Header));
        var opaque = new RepositoryFile(path, bytes, isOpaque: true, gitBlobOid: null);
        Assert.False(RepositoryRules.TryHeader(opaque, out _));
        foreach (var isOpaque in new[] { false, true })
        {
            var supplied = new RepositoryFile(path, ImmutableArray.Create<byte>(0xff), Header, isOpaque);
            Assert.True(RepositoryRules.TryHeader(supplied, out var parsed));
            Assert.Equal(Header.Length, parsed.BodyOffset);
            var empty = new RepositoryFile(path, bytes, string.Empty, isOpaque);
            Assert.False(RepositoryRules.TryHeader(empty, out _));
        }
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void RegisteredHeaderScanDoesNotMaterializeLargeBody(bool utility, bool multiline)
    {
        var header = utility ? Header.Replace("   digest:", "   utility: none\n   digest:", StringComparison.Ordinal) : Header;
        var source = header + string.Concat(Enumerable.Repeat(multiline ? "-- large multiline body 🚀\n" : "x", 300_000));
        var raw = RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(RuleFixture.RingPath, source)]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var context = HeaderContext(snapshot);
        _ = RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(12), HeaderContext(
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(RuleFixture.RingPath, Header)]))).Snapshot));

        var before = GC.GetAllocatedBytesForCurrentThread();
        var result = RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(12), context);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.Empty(result.Diagnostics);
        Assert.True(allocated < source.Length / 4, $"SL-012 allocated {allocated} bytes for {source.Length} characters.");
        var file = Assert.Single(snapshot.Files).Value;
        Assert.Equal(raw.Entries[0].Bytes, file.RawBytes);
        before = GC.GetAllocatedBytesForCurrentThread();
        var materialized = file.Text;
        allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(source, materialized);
        Assert.True(allocated >= source.Length * 2L, "SL-012 had already materialized the full text.");
    }

    [Fact]
    public void RegisteredHeaderScanKeepsGlobalDuplicateGidInfluenceOnMismatchedTarget()
    {
        const string target = "D5/S0/Carrier/Target.lean";
        const string duplicate = "D5/S0/Carrier/Unrelated.lean";
        var entries = new[] { RawRepositoryEntry.FromText(target, Header), RawRepositoryEntry.FromText(duplicate, Header) };
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
        Assert.Empty(RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(12), HeaderContext(snapshot)).Diagnostics);

        snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries.Take(1)))).Snapshot;
        var finding = Assert.Single(RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(12), HeaderContext(snapshot)).Diagnostics);
        Assert.Equal(target, finding.Path);
        Assert.Equal("GID 'D5/S0/Carrier/Ring' does not match 'D5/S0/Carrier/Target'", finding.Message);
    }

    [Fact]
    public void SnapshotStillRejectsInvalidUtf8BeyondHeaderPrefix()
    {
        var bytes = Encoding.UTF8.GetBytes(Header + "\n\nbody\n").Concat(new byte[] { 0xff }).ToImmutableArray();
        var failure = Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([new RawRepositoryEntry(RuleFixture.RingPath, bytes)])));
        Assert.Contains("UTF-8", failure.Message, StringComparison.Ordinal);
    }

    private static CurrentRuleContext HeaderContext(RepositorySnapshot snapshot)
    {
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(TestFileMap.Canonical), Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;
        var selection = CurrentRuleSelection.Create(
            RuleCatalog.Default.CurrentPredicateIds.Select(id => id.Value).ToArray(), ["SL-012"]);
        return CurrentRuleContext.CreateWithoutLean(snapshot, policy, null, selection);
    }

    [Fact]
    public void DecodingValidatesUtf8WithoutMaterializingUnusedText()
    {
        var text = new string('x', 8 * 1024 * 1024);
        var raw = RawRepositorySnapshot.Create([RawRepositoryEntry.FromText("data.json", text)]);
        _ = SnapshotDecoder.Decode(RawRepositorySnapshot.Create([RawRepositoryEntry.FromText("warm.txt", "warm")]));

        var before = GC.GetAllocatedBytesForCurrentThread();
        var decoded = SnapshotDecoder.Decode(raw);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded).Snapshot;
        var file = Assert.Single(snapshot.Files).Value;
        Assert.False(file.HasBom);
        Assert.False(file.HasCarriageReturn);
        Assert.False(file.HasTrailingWhitespace);
        Assert.True(allocated < text.Length,
            $"Decoding allocated {allocated} bytes before any consumer requested text.");
        Assert.Equal(text, file.Text);
        Assert.Same(file.Text, file.Text);
    }

    [Theory]
    [InlineData("", false)]
    [InlineData("\n\n", false)]
    [InlineData("a\nb\n", false)]
    [InlineData("a b\n", false)]
    [InlineData("a\rb\n", false)]
    [InlineData("\tvalue", false)]
    [InlineData("\u00a0\n", false)]
    [InlineData(" ", true)]
    [InlineData("\t", true)]
    [InlineData("\r", true)]
    [InlineData("\r\n", true)]
    [InlineData("a \nb", true)]
    [InlineData("a\t\n\n", true)]
    [InlineData("a\n ", true)]
    [InlineData("\n\nb\r\n\n", true)]
    public void TrailingWhitespacePreservesLineEndingBoundaries(string text, bool expected)
    {
        var decoded = SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            [RawRepositoryEntry.FromText("sample.txt", text)]));

        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded).Snapshot;
        Assert.Equal(expected, Assert.Single(snapshot.Files).Value.HasTrailingWhitespace);
    }

    [Fact]
    public void TrailingWhitespaceInspectionDoesNotAllocatePerLine()
    {
        var text = string.Concat(Enumerable.Repeat("no trailing whitespace\n", 100_000));
        var path = RepoPath.CreateKnown("large.txt");
        var bytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(text));
        _ = new RepositoryFile(path, bytes, "warm\nup\n");

        var before = GC.GetAllocatedBytesForCurrentThread();
        var file = new RepositoryFile(path, bytes, text);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Assert.False(file.HasTrailingWhitespace);
        Assert.True(allocated < text.Length,
            $"Whitespace inspection allocated {allocated} bytes for {text.Length} existing characters.");
    }

    [Fact]
    public void TheoryBytesAreOpaqueAndPreserveInvalidUtf8Exactly()
    {
        var path = string.Concat("docs/develop/", "theory/non-utf8.bin");
        var bytes = ImmutableArray.Create<byte>(0xff, 0x00, 0xfe);
        var raw = RawRepositorySnapshot.Create(
        [
            new RawRepositoryEntry(path, bytes),
        ]);

        var decoded = SnapshotDecoder.Decode(raw);

        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded).Snapshot;
        Assert.True(snapshot.TryGetFile(path, out var file));
        Assert.True(file.IsOpaque);
        Assert.Equal(bytes.ToArray(), file.RawBytes.ToArray());
    }

    [Fact]
    public void NoncanonicalCasNeighborRemainsStrictUtf8()
    {
        var raw = RawRepositorySnapshot.Create(
        [
            new RawRepositoryEntry(
                "Meta/Digestion/atoms/sha256/" + "not-a-hash",
                ImmutableArray.Create<byte>(0xff)),
        ]);

        var decoded = SnapshotDecoder.Decode(raw);

        var failure = Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(decoded);
        Assert.Contains("UTF-8", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SnapshotStrictlyDecodesUtf8WithoutErasingRawAnomalies()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            new RawRepositoryEntry(
                "Evidence/D5/S0/Carrier/Result.run.json",
                ImmutableArray.CreateRange(Encoding.UTF8.GetPreamble().Concat(Encoding.UTF8.GetBytes("{\"value\": 1} \r\n")))),
        });

        var decoded = SnapshotDecoder.Decode(raw);

        var accepted = Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded);
        var file = accepted.Snapshot.Files.Single().Value;
        Assert.True(file.HasBom);
        Assert.True(file.HasCarriageReturn);
        Assert.True(file.HasTrailingWhitespace);
        Assert.Equal(raw.Entries[0].Bytes.ToArray(), file.RawBytes.ToArray());
    }

    [Fact]
    public void SnapshotRejectsInvalidUtf8AsInfrastructureFailure()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            new RawRepositoryEntry("Evidence/D5/S0/Carrier/Result.run.json", ImmutableArray.Create<byte>(0xff)),
        });

        var decoded = SnapshotDecoder.Decode(raw);

        var failure = Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(decoded);
        Assert.Contains("UTF-8", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SnapshotRejectsCaseCollisionsAndTraversalBeforeRulesRun()
    {
        var collision = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText(RuleFixture.RingPath, "a"),
            RawRepositoryEntry.FromText("D5/S0/carrier/Ring.lean", "b"),
        });
        var traversal = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("../D5/S0/Carrier/Ring.lean", "a"),
        });

        Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(SnapshotDecoder.Decode(collision));
        Assert.IsType<SnapshotDecodeOutcome.InfrastructureFailure>(SnapshotDecoder.Decode(traversal));
    }
}
