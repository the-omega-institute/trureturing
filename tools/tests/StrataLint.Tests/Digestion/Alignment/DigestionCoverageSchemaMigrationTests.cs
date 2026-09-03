using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed class DigestionCoverageSchemaMigrationTests
{
    private const string SourceId = "coverage-migration-fixture";
    private const string AtomId =
        "1111111111111111111111111111111111111111111111111111111111111111";
    private const string AtomPath =
        BackfillInventoryLoader.RootPath + SourceId + "/partial-open/" + AtomId + ".yaml";
    private const string FirstGid = "D5/S0/Carrier/CoverageMigrationA";
    private const string SecondGid = "D5/S0/Carrier/CoverageMigrationB";
    private const string ReceiptOnlyGid = "D5/S0/Carrier/CoverageMigrationC";

    [Fact]
    public void MigrationRejectsLegacySourceBindingThatDiffersFromAtomId()
    {
        var (snapshot, lean) = Fixture("sha256:" + new string('f', 64));

        var exception = Assert.Throws<FormatException>(() =>
            DigestionCoverageSchemaMigrator.Migrate(snapshot, lean));

        Assert.Contains("does not match atom_id", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MigrationPreservesLegacyRelationshipUnionAndRecomputesCurrentTargets()
    {
        var (snapshot, lean) = Fixture("sha256:" + AtomId);

        var migration = DigestionCoverageSchemaMigrator.Migrate(snapshot, lean);
        var entry = Assert.Single(migration.Document.RequireDigestionEntries());

        Assert.Equal(2, migration.SourceBindingsValidated);
        Assert.Equal(3, migration.RelationshipsBefore);
        Assert.Equal(3, migration.RelationshipsAfter);
        Assert.Equal(3, migration.ResolvedTargets);
        Assert.Equal(0, migration.NullTargets);
        Assert.Equal(
            [FirstGid, SecondGid, ReceiptOnlyGid],
            entry.Coverage.Select(static edge => edge.Gid).ToArray());
        Assert.Equal(
            new string?[] { Id('a'), Id('b'), Id('c') },
            entry.Coverage.Select(static edge => edge.TargetStatementId).ToArray());
        Assert.DoesNotContain(
            "sha256:" + new string('0', 64),
            Encoding.UTF8.GetString(migration.AtomFiles[AtomPath].AsSpan()),
            StringComparison.Ordinal);
    }

    [Fact]
    public void CanonicalMigrationSecondPassIsByteIdentical()
    {
        var (legacySnapshot, lean) = Fixture("sha256:" + AtomId);
        var first = DigestionCoverageSchemaMigrator.Migrate(legacySnapshot, lean);
        var canonicalSnapshot = ReplaceAtoms(legacySnapshot, first.AtomFiles);

        var second = DigestionCoverageSchemaMigrator.Migrate(canonicalSnapshot, lean);

        Assert.Equal(first.RelationshipsAfter, second.RelationshipsBefore);
        Assert.Equal(first.AtomFiles.Keys.Order(StringComparer.Ordinal),
            second.AtomFiles.Keys.Order(StringComparer.Ordinal));
        foreach (var path in first.AtomFiles.Keys)
        {
            Assert.True(first.AtomFiles[path].AsSpan().SequenceEqual(second.AtomFiles[path].AsSpan()), path);
        }
    }

    private static (RepositorySnapshot Snapshot, AcceptedLeanClosure Lean) Fixture(
        string sourceBinding)
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [BackfillInventoryLoader.RootPath + SourceId + "/source.toml"] = $$"""
                source_id = "{{SourceId}}"
                path = "docs/source.md"
                atomizer = "none"
                genre_registry_check = "no-registry"
                unregistered_genres = []
                """ + "\n",
            [AtomPath] = LegacyAtom(sourceBinding),
            [FirstGid + ".lean"] = LeanSource(FirstGid),
            [SecondGid + ".lean"] = LeanSource(SecondGid),
            [ReceiptOnlyGid + ".lean"] = LeanSource(ReceiptOnlyGid),
        };
        FrozenStatementReceiptTestData.AddLedger(
            files,
            new FrozenStatementReceiptTestData.Module(FirstGid + ".lean", Id('a'), []),
            new FrozenStatementReceiptTestData.Module(SecondGid + ".lean", Id('b'), []),
            new FrozenStatementReceiptTestData.Module(ReceiptOnlyGid + ".lean", Id('c'), []));
        var snapshot = Snapshot(files.Select(static pair =>
            (pair.Key, Encoding.UTF8.GetBytes(pair.Value))).ToArray());
        return (snapshot, AcceptedLean(FirstGid + ".lean", SecondGid + ".lean", ReceiptOnlyGid + ".lean"));
    }

    private static string LegacyAtom(string sourceBinding)
    {
        var relationshipKey = "coverage_" + "gids";
        var sourceKey = "source_" + "sha256";
        var historyKey = "statement_id_" + "history";
        return $$"""
            fingerprints:
              raw_sha256: sha256:{{AtomId}}
              normalized_sha256: sha256:{{AtomId}}
            cas_ref: sha256:{{AtomId}}
            {{relationshipKey}}:
              - {{FirstGid}}
              - {{SecondGid}}
            receipts:
              coverage:
                - gid: {{FirstGid}}
                  {{sourceKey}}: {{sourceBinding}}
                  target_statement_id: sha256:{{new string('0', 64)}}
                  {{historyKey}}: []
                - gid: {{ReceiptOnlyGid}}
                  {{sourceKey}}: sha256:{{AtomId}}
                  target_statement_id: sha256:{{new string('0', 64)}}
              scribe: []
              unresolved_subitems: []
            """ + "\n";
    }

    private static string LeanSource(string gid) => $$"""
        /- GID: {{gid}}
           generality: G
           mirror-B: none(waiver:test)
           mirror-E: none(waiver:test)
           anchors: []
           digest: Coverage migration fixture. -/
        theorem probe : True := by trivial
        """;

    private static RepositorySnapshot ReplaceAtoms(
        RepositorySnapshot snapshot,
        ImmutableDictionary<string, ImmutableArray<byte>> replacements)
    {
        var raw = snapshot.Files.Select(pair => new RawRepositoryEntry(
            pair.Key.Value,
            replacements.GetValueOrDefault(pair.Key.Value, pair.Value.RawBytes)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(raw))).Snapshot;
    }

    private static string Id(char value) => FrozenStatementReceiptTestData.Id(value);
}
