using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed class FakeAtomHistorySource(Func<AtomHistory> read) : IAtomHistorySource
{
    internal int Calls { get; private set; }

    public AtomHistory Read()
    {
        Calls++;
        return read();
    }

    internal static FakeAtomHistorySource ForEntries(IEnumerable<string> atomIds) => new(() =>
        new AtomHistory(false, atomIds.Distinct(StringComparer.Ordinal).ToDictionary(
            static id => id,
            static _ => new DateTimeOffset(2026, 8, 14, 0, 0, 0, TimeSpan.Zero),
            StringComparer.Ordinal)));

    internal static FakeAtomHistorySource ForPaths(IEnumerable<string> paths) =>
        ForEntries(paths.Where(DigestionCasStore.IsCanonicalPath)
            .Select(static path => path[DigestionCasStore.RootPath.Length..]));

    internal static DigestAtomAge Project(
        DigestionLedgerEvaluation evaluation, DigestionFrontierProjection frontier) =>
        DigestAtomAge.Create(evaluation, frontier,
            ForEntries(evaluation.Entries.Select(static item => item.Entry.CasRef["sha256:".Length..])).Read(),
            new DigestAgeClock());
}

internal sealed class DigestAgeClock : TimeProvider
{
    public override DateTimeOffset GetUtcNow() =>
        new(2026, 9, 6, 0, 1, 0, TimeSpan.Zero);
}

internal sealed record DigestAgeFixture(RawRepositorySnapshot Raw, ImmutableArray<string> AtomIds)
{
    internal static DigestAgeFixture Create(int count = 1)
    {
        var files = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText(TheoryAtomizerDataLoader.DataPath, TheoryAtomizerDataTests.Minimal),
        };
        var ids = ImmutableArray.CreateBuilder<string>();
        for (var index = 0; index < count; index++)
        {
            var source = index % 2 == 0 ? "source-a" : "source-b";
            if (index < 2)
            {
                files.Add(RawRepositoryEntry.FromText($"Meta/Digestion/backfill/{source}/source.toml", $$"""
                    source_id = "{{source}}"
                    path = "synthetic/{{source}}.md"
                    atomizer = "none"
                    genre_registry_check = "no-registry"
                    unregistered_genres = []
                    """ + "\n"));
            }

            var capture = DigestionCasStore.Capture(Encoding.UTF8.GetBytes($"synthetic claim {index}\n"));
            var atomId = capture.Reference["sha256:".Length..];
            ids.Add(atomId);
            var fingerprints = DigestionFingerprint.Compute(capture.Bytes.AsSpan());
            var quarantine = index == 1 ? "\n  quarantine:\n    blocker_class: missing-prerequisite\n"
                + "    justification: missing witness\n    reentry_condition: supply witness\n" : "\n";
            files.Add(RawRepositoryEntry.FromText(
                $"Meta/Digestion/backfill/{source}/residual-open/{atomId}.yaml", $$"""
                fingerprints:
                  raw_sha256: {{fingerprints.RawSha256}}
                  normalized_sha256: {{fingerprints.NormalizedSha256}}
                cas_ref: {{capture.Reference}}
                coverage_gids: []
                receipts:
                  scribe: []
                  unresolved_subitems: []
                  chain_atoms: []
                  tail_authorization: null
                """ + quarantine));
            files.Add(new RawRepositoryEntry(capture.RelativePath, capture.Bytes));
        }

        return new DigestAgeFixture(RawRepositorySnapshot.Create(files), ids.ToImmutable());
    }

    internal CommandResult Run(IAtomHistorySource history, string option = "--json")
    {
        var before = Raw.Entries.Select(static entry => (entry.Path, Bytes: entry.Bytes.ToArray())).ToArray();
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), Raw, Raw);
        var result = DigestStatusCommand.Run(
            gateway,
            new FakeLeanReportSource(LeanAxiomReport.Create(
                new Dictionary<string, LeanFileReport>(StringComparer.Ordinal))),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty),
            [option], history, new DigestAgeClock());
        Assert.Equal(before.Length, Raw.Entries.Length);
        for (var index = 0; index < before.Length; index++)
        {
            Assert.Equal(before[index].Path, Raw.Entries[index].Path);
            Assert.Equal(before[index].Bytes, Raw.Entries[index].Bytes.ToArray());
        }

        return result;
    }
}
