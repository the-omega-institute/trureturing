using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// A theory document that nobody has declared a source for is the hole this closes: before
/// this, it sat in the tree undigested and no machine said so. Ingest now derives the
/// declaration from the path and digests it with the default atomizer, so "a volume nobody
/// wrote a dialect for" is a state the ledger reaches on its own rather than a state that
/// waits for a hand-written file.
/// </summary>
public sealed class DefaultTheorySourceTests
{
    private const string DeclaredPath = "docs/develop/theory/DECLARED.md";
    private const string UndeclaredPath = "docs/develop/theory/UNDECLARED_VOLUME.md";
    private const string Markdown = "# 未声明卷\n\n## 定理 1.1\n\n证。\n";

    private static DigestionIngestPlan PlanWith(params (string Path, byte[] Bytes)[] extraFiles)
    {
        var declaredBytes = Encoding.UTF8.GetBytes("# 已声明卷\n\n## 定理 9.9\n\n证。\n");
        var declared = GenericAtomizer.Atomize(declaredBytes, TheoryAtomizerRules.None);
        var atom = Assert.Single(declared.Claims);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var entry = DigestionTestSupport.Entry(
            atom,
            atom.Fingerprints.RawSha256["sha256:".Length..],
            AtomizerRegistry.GenericId,
            sourceId: "declared",
            sourcePath: DeclaredPath,
            casRef: capture.Reference);
        var ledger = DigestionTestSupport.Document(
            AtomizerRegistry.GenericId,
            [entry],
            "declared",
            DeclaredPath,
            GenreRegistryCheck.Collected([]));
        var files = extraFiles
            .Append((DeclaredPath, declaredBytes))
            .Append((capture.RelativePath, capture.Bytes.ToArray()))
            .ToArray();

        return DigestionIngestor.Plan(ledger, DigestionTestSupport.Snapshot(files), ledger);
    }

    [Fact]
    public void ATheoryDocumentWithNoDeclaredSourceIsRegisteredWithTheDefaultAtomizer()
    {
        var plan = PlanWith((UndeclaredPath, Encoding.UTF8.GetBytes(Markdown)));

        var registered = Assert.Single(
            plan.Document.RequireDigestionSources().Where(static source => source.SourceId != "declared"));
        Assert.Equal("undeclared-volume", registered.SourceId);
        Assert.Equal(UndeclaredPath, registered.SourcePath);
        Assert.Equal(AtomizerRegistry.GenericId, registered.Atomizer);
    }

    [Fact]
    public void TheRegisteredSourceIsDigestedInTheSamePassRatherThanLeftEmpty()
    {
        var plan = PlanWith((UndeclaredPath, Encoding.UTF8.GetBytes(Markdown)));

        var registered = plan.Document.RequireDigestionSources()
            .Single(static source => source.SourceId == "undeclared-volume");
        var expectedFingerprint = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes("## 定理 1.1\n\n证。\n")).RawSha256;
        Assert.Equal(
            [expectedFingerprint],
            registered.Entries.Select(static entry => entry.Fingerprints.RawSha256).ToArray());
        Assert.All(registered.Entries, entry =>
            Assert.Equal(expectedFingerprint["sha256:".Length..], entry.AtomId));
    }

    [Fact]
    public void ADocumentOutsideTheTheoryRootIsNotRegistered()
    {
        var plan = PlanWith(("docs/develop/spec/some-spec.md", Encoding.UTF8.GetBytes(Markdown)));

        Assert.Equal(
            ["declared"],
            plan.Document.RequireDigestionSources()
                .Select(static source => source.SourceId)
                .ToArray());
    }

    [Fact]
    public void AnAlreadyDeclaredDocumentIsNotRegisteredTwice()
    {
        var plan = PlanWith();

        Assert.Equal(
            ["declared"],
            plan.Document.RequireDigestionSources()
                .Select(static source => source.SourceId)
                .ToArray());
    }

    /// <summary>
    /// Not Markdown, so the default atomizer finds no claim in it. That is the one case the
    /// existing coarse fallback is for, and it must still land there — accounted as one
    /// whole-file atom with a stated reason, never silently skipped.
    /// </summary>
    [Fact]
    public void ANonMarkdownTheoryFileIsRegisteredAndFallsBackToOneWholeFileAtom()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("{\"a\":1}\n{\"a\":2}\n");
        var plan = PlanWith((
            "docs/develop/theory/VOLUME_registry.jsonl",
            sourceBytes));

        var fallback = Assert.Single(plan.Fallbacks);
        Assert.Equal("volume-registry", fallback.SourceId);
        var registered = plan.Document.RequireDigestionSources()
            .Single(static source => source.SourceId == "volume-registry");
        Assert.Equal(
            [DigestionFingerprint.Compute(sourceBytes).RawSha256],
            registered.Entries.Select(static entry => entry.Fingerprints.RawSha256).ToArray());
    }

    /// <summary>
    /// The derived id is a function of the file name, so two file names that slug to the
    /// same id would silently share a ledger directory. Fail closed and name both paths.
    /// </summary>
    [Fact]
    public void TwoFileNamesThatDeriveTheSameSourceIdAreRefused()
    {
        var error = Assert.Throws<FormatException>(() => PlanWith(
            ("docs/develop/theory/SAME_NAME.md", Encoding.UTF8.GetBytes(Markdown)),
            ("docs/develop/theory/same-name.md", Encoding.UTF8.GetBytes(Markdown))));

        Assert.Contains("same-name", error.Message, StringComparison.Ordinal);
        Assert.Contains("SAME_NAME.md", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ADerivedSourceIdThatCollidesWithADeclaredOneIsRefused()
    {
        var error = Assert.Throws<FormatException>(() => PlanWith(
            ("docs/develop/theory/DECLARED_.md", Encoding.UTF8.GetBytes(Markdown))));

        Assert.Contains("declared", error.Message, StringComparison.Ordinal);
    }
}
