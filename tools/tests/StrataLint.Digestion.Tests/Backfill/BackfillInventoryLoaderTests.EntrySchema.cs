using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void WriteAtomSortsCoverageGidsOrdinally()
    {
        var written = System.Text.Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteAtom(CoverageOrderEntry()).AsSpan());

        Assert.Contains("coverage_gids:\n" + ExpectedOrderedCoverage("  "), written, StringComparison.Ordinal);
    }

    [Fact]
    public void WriteEntrySortsCoverageGidsOrdinally()
    {
        var written = System.Text.Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteEntry(CoverageOrderEntry()).AsSpan());

        Assert.Contains("        coverage_gids:\n" + ExpectedOrderedCoverage("          "), written, StringComparison.Ordinal);
    }

    [Fact]
    public void StatusAuthorityIdentityIgnoresCoverageOrder()
    {
        var entry = CoverageOrderEntry();
        var source = CoverageOrderSource(entry);
        var reordered = entry with { Coverage = [entry.Coverage[1], entry.Coverage[0]] };

        Assert.Equal(
            BackfillInventoryWriter.WriteStatusAuthorityIdentity(source, entry).ToArray(),
            BackfillInventoryWriter.WriteStatusAuthorityIdentity(source, reordered).ToArray());
    }

    [Fact]
    public void StatusAuthorityIdentityRejectsChangedCoverageTarget()
    {
        var entry = CoverageOrderEntry();
        var source = CoverageOrderSource(entry);
        var changed = entry with
        {
            Coverage = [entry.Coverage[0] with { TargetStatementId = null }, entry.Coverage[1]],
        };

        Assert.False(BackfillInventoryWriter.WriteStatusAuthorityIdentity(source, entry).AsSpan()
            .SequenceEqual(BackfillInventoryWriter.WriteStatusAuthorityIdentity(source, changed).AsSpan()));
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void CoverageWriterRejectsDuplicateGid(bool fullEntry, bool conflictingTarget)
    {
        var entry = CoverageOrderEntry();
        var duplicate = entry.Coverage[0] with
        {
            TargetStatementId = conflictingTarget ? "sha256:" + new string('b', 64) : entry.Coverage[0].TargetStatementId,
        };
        entry = entry with { Coverage = entry.Coverage.Add(duplicate) };

        var exception = Assert.Throws<InvalidOperationException>(() => fullEntry
            ? BackfillInventoryWriter.WriteEntry(entry)
            : BackfillInventoryWriter.WriteAtom(entry));

        Assert.Contains("BACKFILL_COVERAGE_DUPLICATE_GID", exception.Message, StringComparison.Ordinal);
        Assert.Contains(duplicate.Gid, exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CoverageLoaderRejectsNonOrdinalGidOrder(bool baseline)
    {
        var atom = CanonicalCoverageAtom("coverage_gids:\n"
            + "  - gid: D5/S0/Carrier/Probe.alpha\n    target_statement_id: null\n"
            + "  - gid: D5/S0/Carrier/Probe.Zeta\n    target_statement_id: null");
        var snapshot = Snapshot(Source("delta-v0.1", "docs/delta.md", "none"), atom);

        var exception = Assert.Throws<FormatException>(() => baseline
            ? BackfillInventoryLoader.LoadBaseline(snapshot)
            : BackfillInventoryLoader.Load(snapshot));

        Assert.Equal(
            $"BACKFILL_COVERAGE_ORDER: entry {FixtureAtomId("theorem/canonical-coverage")} coverage_gids must have unique gids in ordinal order",
            exception.Message);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CoverageLoaderAcceptsOrdinalGidOrder(bool baseline)
    {
        var atom = CanonicalCoverageAtom("coverage_gids:\n" + ExpectedOrderedCoverage("  ").TrimEnd('\n'));
        var snapshot = Snapshot(Source("delta-v0.1", "docs/delta.md", "none"), atom);

        var document = baseline
            ? BackfillInventoryLoader.LoadBaseline(snapshot)
            : BackfillInventoryLoader.Load(snapshot);

        var entry = Assert.Single(document.RequireDigestionEntries());
        Assert.Equal(["D5/S0/Carrier/Probe.Zeta", "D5/S0/Carrier/Probe.alpha"], entry.CoverageGids.ToArray());
        Assert.Null(entry.Coverage[0].TargetStatementId);
        Assert.Equal("sha256:" + new string('a', 64), entry.Coverage[1].TargetStatementId);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void CoverageLoaderRejectsDuplicateGid(bool baseline, bool conflictingTarget)
    {
        var target = conflictingTarget ? "sha256:" + new string('a', 64) : "null";
        var atom = CanonicalCoverageAtom("coverage_gids:\n"
            + "  - gid: D5/S0/Carrier/Probe.alpha\n    target_statement_id: null\n"
            + $"  - gid: D5/S0/Carrier/Probe.alpha\n    target_statement_id: {target}");
        var snapshot = Snapshot(Source("delta-v0.1", "docs/delta.md", "none"), atom);

        var exception = Assert.Throws<FormatException>(() => baseline
            ? BackfillInventoryLoader.LoadBaseline(snapshot)
            : BackfillInventoryLoader.Load(snapshot));

        Assert.Contains("BACKFILL_COVERAGE_ORDER", exception.Message, StringComparison.Ordinal);
    }

    private static DigestionLedgerSource CoverageOrderSource(DigestionLedgerEntry entry) => new(
        entry.SourceId, entry.SourcePath, entry.Atomizer, [],
        GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry), [entry]);

    private static DigestionLedgerEntry CoverageOrderEntry()
    {
        var atom = CanonicalCoverageAtom("coverage_gids: []");
        var entry = Assert.Single(BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"), atom)).RequireDigestionEntries());
        return entry with
        {
            Coverage =
            [
                new DigestionCoverageEdge("D5/S0/Carrier/Probe.alpha", "sha256:" + new string('a', 64)),
                new DigestionCoverageEdge("D5/S0/Carrier/Probe.Zeta", null),
            ],
        };
    }

    private static string ExpectedOrderedCoverage(string indent) =>
        $"{indent}- gid: D5/S0/Carrier/Probe.Zeta\n{indent}  target_statement_id: null\n"
        + $"{indent}- gid: D5/S0/Carrier/Probe.alpha\n{indent}  target_statement_id: sha256:{new string('a', 64)}\n";

    [Fact]
    public void DirectoryAtomAcceptsCanonicalCoverageEdgesAndDerivesCoverageGids()
    {
        const string gid = "D5/S0/Carrier/Probe.probe";
        var atom = CanonicalCoverageAtom($$"""
            coverage_gids:
              - gid: {{gid}}
                target_statement_id: null
            """);

        var entry = Assert.Single(BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            atom)).RequireDigestionEntries());

        Assert.Equal([gid], entry.CoverageGids.ToArray());
        var edge = Assert.Single(entry.Coverage);
        Assert.Equal(gid, edge.Gid);
        Assert.Null(edge.TargetStatementId);
    }

    [Theory]
    [InlineData("coverage-key", false)]
    [InlineData("receipts-coverage", false)]
    [InlineData("receipts-coverage", true)]
    [InlineData("source-sha", false)]
    [InlineData("statement-history", false)]
    [InlineData("recorded-at", false)]
    [InlineData("recorded-at", true)]
    public void DirectoryAtomRejectsEachRetiredCoverageField(string retiredField, bool baseline)
    {
        var sourceKey = "source_" + "sha256";
        var historyKey = "statement_id_" + "history";
        const string retiredRelationshipKey = "coverage";
        var recordedKey = "recorded_at_" + "utc";
        var coverage = retiredField switch
        {
            "source-sha" => $$"""
                coverage_gids:
                  - gid: D5/S0/Carrier/Probe.probe
                    target_statement_id: null
                    {{sourceKey}}: sha256:0000000000000000000000000000000000000000000000000000000000000000
                """,
            "statement-history" => $$"""
                coverage_gids:
                  - gid: D5/S0/Carrier/Probe.probe
                    target_statement_id: null
                    {{historyKey}}: []
                """,
            "receipts-coverage" or "recorded-at" => """
                coverage_gids:
                  - gid: D5/S0/Carrier/Probe.probe
                    target_statement_id: null
                """,
            _ => "coverage_gids: []",
        };
        var atom = CanonicalCoverageAtom(coverage);
        atom = retiredField switch
        {
            "coverage-key" => (atom.Path, atom.Text.Replace(
                "coverage_gids: []\n",
                $"coverage_gids: []\n{retiredRelationshipKey}: []\n",
                StringComparison.Ordinal)),
            "receipts-coverage" => (atom.Path, atom.Text.Replace(
                "receipts:\n",
                "receipts:\n  coverage: []\n",
                StringComparison.Ordinal)),
            "recorded-at" => (atom.Path, atom.Text.Replace(
                "  unresolved_subitems: []\n",
                "  unresolved_subitems: []\n"
                + "  cover_disposition:\n"
                + "    outcome: partial-open\n"
                + "    gids:\n"
                + "      - D5/S0/Carrier/Probe.probe\n"
                + "    gaps: []\n"
                + $"    {recordedKey}: 2026-09-03T00:00:00.0000000+00:00\n",
                StringComparison.Ordinal)),
            _ => atom,
        };

        var snapshot = Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            atom);
        var exception = Assert.Throws<FormatException>(() =>
            baseline
                ? BackfillInventoryLoader.LoadBaseline(snapshot)
                : BackfillInventoryLoader.Load(snapshot));

        var expectedMessage = retiredField switch
        {
            "receipts-coverage" => "receipts keys are not canonical",
            "recorded-at" => "cover_disposition keys are not canonical",
            "source-sha" or "statement-history" => "coverage edge keys are not canonical",
            _ => "source delta-v0.1 entry keys are not canonical",
        };
        Assert.Contains(expectedMessage, exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineCanonicalSchemaRejectsRetiredCoverageKey()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadBaseline(Snapshot(
                Source("delta-v0.1", "docs/delta.md", "none"),
                (atom.Path, atom.Text + "coverage: []\n"))));

        Assert.Equal("source delta-v0.1 entry keys are not canonical", exception.Message);
    }

    [Fact]
    public void BaselineDirectoryProjectsHistoricalChainAtomReferencesToContentIdentity()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var parent = Atom("delta-v0.1", "residual-open", "parent", "theorem/parent");
        var child = Atom("delta-v0.1", "residual-open", "child", "theorem/child");
        var childText = child.Text.Replace(
            "  chain_atoms: []\n",
            "  chain_atoms:\n    - legacy-parent\n",
            StringComparison.Ordinal);
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            source,
            ($"{BackfillInventoryLoader.RootPath}delta-v0.1/residual-open/legacy-parent.yaml", parent.Text),
            ($"{BackfillInventoryLoader.RootPath}delta-v0.1/residual-open/legacy-child.yaml", childText)));

        var projectedChild = document.RequireDigestionEntries()
            .Single(entry => entry.AtomId == FixtureAtomId("theorem/child"));
        Assert.Equal([FixtureAtomId("theorem/parent")], projectedChild.Receipts.ChainAtoms.ToArray());
    }

    [Fact]
    public void DirectoryAtomWriterEscapesSingleQuotesInQuotedScalars()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta", "theorem/delta");
        var text = atom.Text.Replace(
            "  tail_authorization: null\n",
            "  tail_authorization: null\n"
            + "  quarantine:\n"
            + "    justification: \"source's theorem: missing\"\n"
            + "    reentry_condition: retry\n"
            + "    blocker_class: missing-prerequisite\n",
            StringComparison.Ordinal);
        var entry = Assert.Single(BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, text))).RequireDigestionEntries());

        var written = System.Text.Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());

        Assert.Contains("justification: \"source's theorem: missing\"", written, StringComparison.Ordinal);
        var roundTripped = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, written)));
        Assert.Equal("source's theorem: missing", Assert.Single(roundTripped.RequireDigestionEntries())
            .Receipts.Quarantine?.Justification);
    }

    private static (string Path, string Text) CanonicalCoverageAtom(string coverage)
    {
        var fingerprint = "sha256:" + FixtureAtomId("theorem/canonical-coverage");
        return ($"{BackfillInventoryLoader.RootPath}delta-v0.1/partial-open/{fingerprint["sha256:".Length..]}.yaml", $$"""
            fingerprints:
              raw_sha256: {{fingerprint}}
              normalized_sha256: {{fingerprint}}
            cas_ref: {{fingerprint}}
            {{coverage}}
            receipts:
              unresolved_subitems: []
            """ + "\n");
    }
}
