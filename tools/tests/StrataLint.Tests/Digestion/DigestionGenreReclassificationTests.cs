using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void IngestReclassifiesAnExactlyRegisteredOpenGenreInPlace()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# QDO\n\n## 未登记体 40.2\n\nopen。\n");
        var empty = DigestionTestSupport.EmptyDocument("dialect:qdo");
        var first = DigestionIngestor.Plan(
            empty,
            DigestionTestSupport.Snapshot(("docs/source.md", sourceBytes)),
            empty);
        var openSource = Assert.Single(first.Document.RequireDigestionSources());
        var openEntry = Assert.Single(openSource.Entries);

        var second = DigestionIngestor.Plan(
            first.Document,
            SnapshotWithRules(sourceBytes, first.CasObjects, QdoRulesWithRegisteredProbeGenre()),
            first.Document);

        var reclassifiedSource = Assert.Single(second.Document.RequireDigestionSources());
        var reclassified = Assert.Single(reclassifiedSource.Entries);
        Assert.Equal("unregistered/%E6%9C%AA%E7%99%BB%E8%AE%B0%E4%BD%93/40.2", openEntry.AstPath);
        Assert.Equal("remark/40.2", reclassified.AstPath);
        Assert.Equal(openEntry.AtomId, reclassified.AtomId);
        Assert.Equal(openEntry.CasRef, reclassified.CasRef);
        Assert.Equal(openEntry.Fingerprints, reclassified.Fingerprints);
        Assert.Equal(openEntry.Receipts, reclassified.Receipts);
        Assert.Equal(GenreRegistryCheckKind.Collected, reclassifiedSource.GenreRegistryCheck.Kind);
        Assert.Empty(reclassifiedSource.GenreRegistryCheck.UnregisteredGenres);
        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
    }

    [Fact]
    public void IngestReclassifiesAnOpenGenreRegisteredByDeclaredDialectSuffixInPlace()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# QDO\n\n## 极端猜想 40.3\n\nopen。\n");
        var empty = DigestionTestSupport.EmptyDocument("dialect:qdo");
        var first = DigestionIngestor.Plan(
            empty,
            DigestionTestSupport.Snapshot(("docs/source.md", sourceBytes)),
            empty);
        var openSource = Assert.Single(first.Document.RequireDigestionSources());
        var openEntry = Assert.Single(openSource.Entries);

        var second = DigestionIngestor.Plan(
            first.Document,
            SnapshotWithRules(sourceBytes, first.CasObjects, QdoRulesWithConjectureSuffix()),
            first.Document);

        var reclassifiedSource = Assert.Single(second.Document.RequireDigestionSources());
        var reclassified = Assert.Single(reclassifiedSource.Entries);
        Assert.Equal(UnregisteredGenreLocator.ForNumbered("极端猜想", "40.3"), openEntry.AstPath);
        Assert.Equal("observation/40.3", reclassified.AstPath);
        Assert.Equal(openEntry.AtomId, reclassified.AtomId);
        Assert.Equal(openEntry.CasRef, reclassified.CasRef);
        Assert.Equal(openEntry.Receipts, reclassified.Receipts);
        Assert.Empty(reclassifiedSource.GenreRegistryCheck.UnregisteredGenres);
        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
    }

    [Fact]
    public void IngestRejectsOpenGenreReclassificationWhenCanonicalPathIsOccupied()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# QDO\n\n## 未登记体 40.2\n\nopen。\n");
        var empty = DigestionTestSupport.EmptyDocument("dialect:qdo");
        var first = DigestionIngestor.Plan(
            empty,
            DigestionTestSupport.Snapshot(("docs/source.md", sourceBytes)),
            empty);
        var openSource = Assert.Single(first.Document.RequireDigestionSources());
        var openEntry = Assert.Single(openSource.Entries);
        var collision = first.Document.WithDigestionSources(
        [
            openSource with
            {
                Entries = openSource.Entries.Add(openEntry with
                {
                    AtomId = "occupied-canonical-path",
                    AstPath = "remark/40.2",
                }),
            },
        ]);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            collision,
            SnapshotWithRules(sourceBytes, first.CasObjects, QdoRulesWithRegisteredProbeGenre()),
            collision));

        Assert.Contains(
            "genre reclassification ast_path collides: remark/40.2",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRejectsAmbiguousOpenGenreReclassification()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# QDO\n\n## 未登记体 40.2\n\nopen。\n");
        var empty = DigestionTestSupport.EmptyDocument("dialect:qdo");
        var first = DigestionIngestor.Plan(
            empty,
            DigestionTestSupport.Snapshot(("docs/source.md", sourceBytes)),
            empty);
        var openSource = Assert.Single(first.Document.RequireDigestionSources());
        var openEntry = Assert.Single(openSource.Entries);
        var ambiguous = first.Document.WithDigestionSources(
        [
            openSource with
            {
                Entries = openSource.Entries.Add(openEntry with
                {
                    AtomId = "ambiguous-open-candidate",
                }),
            },
        ]);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ambiguous,
            SnapshotWithRules(sourceBytes, first.CasObjects, QdoRulesWithRegisteredProbeGenre()),
            ambiguous));

        Assert.Contains(
            "genre reclassification is ambiguous: remark/40.2",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestDoesNotReclassifyAnOpenGenreWhenRawShaDiffers()
    {
        var originalBytes = Encoding.UTF8.GetBytes("# QDO\n\n## 未登记体 40.2\n\nopen。\n");
        var changedBytes = Encoding.UTF8.GetBytes("# QDO\n\n## 未登记体 40.2\n\nchanged。\n");
        var empty = DigestionTestSupport.EmptyDocument("dialect:qdo");
        var first = DigestionIngestor.Plan(
            empty,
            DigestionTestSupport.Snapshot(("docs/source.md", originalBytes)),
            empty);
        var openEntry = Assert.Single(Assert.Single(first.Document.RequireDigestionSources()).Entries);

        var second = DigestionIngestor.Plan(
            first.Document,
            SnapshotWithRules(changedBytes, first.CasObjects, QdoRulesWithRegisteredProbeGenre()),
            first.Document);

        var entries = Assert.Single(second.Document.RequireDigestionSources()).Entries;
        var preserved = Assert.Single(entries.Where(entry => entry.AtomId == openEntry.AtomId));
        Assert.Equal(openEntry.AstPath, preserved.AstPath);
    }

    [Fact]
    public void IngestDoesNotReclassifyAnOpenGenreWhenMarkerTokenWasNotCollected()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# QDO\n\n## 未登记体 40.2\n\nopen。\n");
        var empty = DigestionTestSupport.EmptyDocument("dialect:qdo");
        var first = DigestionIngestor.Plan(
            empty,
            DigestionTestSupport.Snapshot(("docs/source.md", sourceBytes)),
            empty);
        var openSource = Assert.Single(first.Document.RequireDigestionSources());
        var openEntry = Assert.Single(openSource.Entries);
        var withoutMarker = first.Document.WithDigestionSources(
        [
            openSource with
            {
                GenreRegistryProjection = GenreRegistryProjection.Available(
                    GenreRegistryCheck.Collected(["另一体"])),
            },
        ]);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            withoutMarker,
            SnapshotWithRules(sourceBytes, first.CasObjects, QdoRulesWithRegisteredProbeGenre()),
            withoutMarker));

        Assert.Contains(
            $"ingest residual atom_id collides with the ledger: {openEntry.AtomId}",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestDoesNotReclassifyAnEntryOutsideTheUnregisteredNamespace()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# QDO\n\n## 未登记体 40.2\n\nopen。\n");
        var empty = DigestionTestSupport.EmptyDocument("dialect:qdo");
        var first = DigestionIngestor.Plan(
            empty,
            DigestionTestSupport.Snapshot(("docs/source.md", sourceBytes)),
            empty);
        var openSource = Assert.Single(first.Document.RequireDigestionSources());
        var openEntry = Assert.Single(openSource.Entries);
        var outsideNamespace = first.Document.WithDigestionSources(
        [
            openSource with
            {
                Entries =
                [
                    openEntry with
                    {
                        AstPath = "open-address/"
                            + Uri.EscapeDataString("未登记体")
                            + "/40.2",
                    },
                ],
            },
        ]);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            outsideNamespace,
            SnapshotWithRules(sourceBytes, first.CasObjects, QdoRulesWithRegisteredProbeGenre()),
            outsideNamespace));

        Assert.Contains(
            $"ingest residual atom_id collides with the ledger: {openEntry.AtomId}",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestDoesNotReclassifyWhenRegistryDoesNotResolveTokenToCanonicalPath()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# QDO\n\n## 未登记体 40.2\n\nopen。\n");
        var empty = DigestionTestSupport.EmptyDocument("dialect:qdo");
        var first = DigestionIngestor.Plan(
            empty,
            DigestionTestSupport.Snapshot(("docs/source.md", sourceBytes)),
            empty);
        var snapshot = SnapshotWithRules(
            sourceBytes,
            first.CasObjects,
            QdoRulesWithRegisteredProbeGenre());
        var rules = TheoryAtomizerDataLoader.Load(snapshot);
        var canonical = DeclaredDialectAtomizer.Atomize("dialect:qdo", sourceBytes, rules);
        var mismatched = new AtomizedTheoryDocument(
            [Assert.Single(canonical.Claims) with { AstPath = "theorem/40.2" }],
            canonical.Slices,
            canonical.ClausePlans,
            canonical.GenreRegistryCheck);

        var alignment = DigestionLedgerAligner.Evaluate(
            first.Document,
            snapshot,
            first.Document,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => mismatched);

        Assert.Empty(alignment.GenreReclassifications);
    }

    private static byte[] QdoRulesWithRegisteredProbeGenre()
    {
        const string suffix = "[[dialect.genre_suffix]]\ndialect = \"qdo\"\nsuffix = \"例\"";
        const string exact = "[[dialect.genre]]\ndialect = \"qdo\"\ntoken = \"未登记体\"\nkind = \"remark\"\n\n";
        var rules = Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes);
        Assert.Contains(suffix, rules, StringComparison.Ordinal);
        return Encoding.UTF8.GetBytes(rules.Replace(suffix, exact + suffix, StringComparison.Ordinal));
    }

    private static byte[] QdoRulesWithConjectureSuffix()
    {
        var rules = Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes);
        return Encoding.UTF8.GetBytes(rules + "\n[[dialect.genre_suffix]]\n"
            + "dialect = \"qdo\"\n"
            + "suffix = \"猜想\"\n");
    }

    private static RepositorySnapshot SnapshotWithRules(
        byte[] sourceBytes,
        IEnumerable<DigestionCasObject> casObjects,
        byte[] rulesBytes) => DigestionTestSupport.Snapshot(
            casObjects.Select(static item => (item.RelativePath, item.Bytes.ToArray()))
                .Prepend(("docs/source.md", sourceBytes))
                .Append((TheoryAtomizerDataLoader.DataPath, rulesBytes))
                .ToArray());
}
