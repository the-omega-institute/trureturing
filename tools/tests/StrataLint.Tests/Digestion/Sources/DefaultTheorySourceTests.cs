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

    private static string Ledger(string entry) => string.Join(
        "\n",
        "schema_version: 3",
        "ledger: theory-digestion-v1",
        "sources:",
        "  - source_id: declared",
        "    path: " + DeclaredPath,
        "    atomizer: " + AtomizerRegistry.GenericId,
        "    entries:",
        entry,
        "ticket_index: []");

    private static string Entry(DigestionAtom atom, string casRef) => string.Join(
        "\n",
        "      - atom_id: generic-residual-" + atom.Fingerprints.RawSha256["sha256:".Length..],
        "        ast_path: " + atom.AstPath,
        "        fingerprints:",
        "          raw_sha256: " + atom.Fingerprints.RawSha256,
        "          normalized_sha256: " + atom.Fingerprints.NormalizedSha256,
        "        cas_ref: " + casRef,
        "        coverage_gids: []",
        "        receipts:",
        "          coverage: []",
        "          scribe: []",
        "          unresolved_subitems: []",
        "          chain_atoms: []",
        "          tail_authorization: null",
        "        status:",
        "          migration: residual",
        "          truth: open");

    private static DigestionIngestPlan PlanWith(params (string Path, byte[] Bytes)[] extraFiles)
    {
        var declaredBytes = Encoding.UTF8.GetBytes("# 已声明卷\n\n## 定理 9.9\n\n证。\n");
        var declared = GenericAtomizer.Atomize(declaredBytes, TheoryAtomizerRules.None);
        var atom = declared.Claims.First(static claim => claim.AstPath == "定理/9.9");
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(Entry(atom, capture.Reference)));
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
        Assert.Equal(
            ["定理/1.1"],
            registered.Entries.Select(static entry => entry.AstPath).ToArray());
        Assert.All(registered.Entries, static entry =>
            Assert.StartsWith("generic-residual-", entry.AtomId, StringComparison.Ordinal));
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
        var plan = PlanWith((
            "docs/develop/theory/VOLUME_registry.jsonl",
            Encoding.UTF8.GetBytes("{\"a\":1}\n{\"a\":2}\n")));

        var fallback = Assert.Single(plan.Fallbacks);
        Assert.Equal("volume-registry", fallback.SourceId);
        var registered = plan.Document.RequireDigestionSources()
            .Single(static source => source.SourceId == "volume-registry");
        Assert.Equal(["coarse/source"], registered.Entries.Select(static entry => entry.AstPath).ToArray());
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
