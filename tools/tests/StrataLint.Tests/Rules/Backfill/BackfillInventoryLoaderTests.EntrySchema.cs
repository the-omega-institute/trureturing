using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void DirectoryAtomAcceptsCanonicalCoverageEdgesAndDerivesCoverageGids()
    {
        const string gid = "D5/S0/Carrier/Probe.probe";
        var atom = CanonicalCoverageAtom($$"""
            coverage:
              - gid: {{gid}}
                target_statement_id: null
            """);

        var entry = Assert.Single(BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            atom)).RequireDigestionEntries());

        Assert.Equal([gid], entry.CoverageGids.ToArray());
        var coverageProperty = entry.GetType().GetProperty("Coverage");
        Assert.NotNull(coverageProperty);
        var edge = Assert.Single(Assert.IsAssignableFrom<System.Collections.IEnumerable>(
            coverageProperty!.GetValue(entry)).Cast<object>());
        Assert.Equal(gid, edge.GetType().GetProperty("Gid")?.GetValue(edge));
        Assert.Null(edge.GetType().GetProperty("TargetStatementId")?.GetValue(edge));
    }

    [Theory]
    [InlineData("coverage-gids")]
    [InlineData("receipts-coverage")]
    [InlineData("source-sha")]
    [InlineData("statement-history")]
    [InlineData("recorded-at")]
    public void DirectoryAtomRejectsEachRetiredCoverageField(string retiredField)
    {
        var sourceKey = "source_" + "sha256";
        var historyKey = "statement_id_" + "history";
        var relationshipKey = "coverage_" + "gids";
        var recordedKey = "recorded_at_" + "utc";
        var coverage = retiredField switch
        {
            "source-sha" => $$"""
                coverage:
                  - gid: D5/S0/Carrier/Probe.probe
                    target_statement_id: null
                    {{sourceKey}}: sha256:0000000000000000000000000000000000000000000000000000000000000000
                """,
            "statement-history" => $$"""
                coverage:
                  - gid: D5/S0/Carrier/Probe.probe
                    target_statement_id: null
                    {{historyKey}}: []
                """,
            _ => "coverage: []",
        };
        var atom = CanonicalCoverageAtom(coverage);
        atom = retiredField switch
        {
            "coverage-gids" => (atom.Path, atom.Text.Replace(
                "coverage: []\n",
                $"coverage: []\n{relationshipKey}: []\n",
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

        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            atom)));

        Assert.Contains("keys are not canonical", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineDirectoryAtomAllowsUnknownHistoricalKeyButStillRequiresCurrentFields()
    {
        var currentAtomId = FixtureAtomId("theorem/delta");
        var source = Source("delta-v0.1", "docs/delta.md", "none") with
        {
            Text = Source("delta-v0.1", "docs/delta.md", "none").Text
                + "acknowledged_stale = [\"legacy-delta\"]\n",
        };
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var legacyAtomPath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/residual-open/legacy-delta.yaml";
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            source,
            (legacyAtomPath, atom.Text + "ast_path: theorem/delta\n")));

        Assert.Equal(currentAtomId, Assert.Single(document.RequireDigestionEntries()).AtomId);
        Assert.Equal([currentAtomId], Assert.Single(document.RequireDigestionSources()).AcknowledgedStale.ToArray());

        var missingRequiredField = atom.Text.Replace(
            "coverage: []\n",
            string.Empty,
            StringComparison.Ordinal);
        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadBaseline(Snapshot(
                source,
                (atom.Path, missingRequiredField))));

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
            + "    reentry_condition: retry\n",
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
              scribe: []
              unresolved_subitems: []
            """ + "\n");
    }
}
