using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class NonpropositionalTestSupport
{
    internal const string State = "nonpropositional-inapplicable";
    internal const string Reason = "The neighboring claims make this a transition with no proposition.";
    internal static string Receipt(string previous = "null", string next = "null") =>
        "  nonpropositional:\n"
        + $"    justification: {Reason}\n"
        + $"    previous_atom_id: {previous}\n"
        + $"    next_atom_id: {next}\n";

    internal static string StateName(DigestionStatus status) =>
        DigestionStatusNames.Migration(status.Migration) + "-" + DigestionStatusNames.Truth(status.Truth);

    internal static string PathFor(DigestionLedgerEntry entry, string? state = null) =>
        BackfillInventoryLoader.RootPath + entry.SourceId + "/" + (state ?? StateName(entry.ProjectedStatus))
        + "/" + entry.AtomId + ".yaml";

    internal static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

    internal static DigestionLedgerEntry Settled(DigestionLedgerEntry entry, string? receipt = null)
    {
        var source = DigestionTestSupport.Document(entry.Atomizer, [entry]).RequireDigestionSources().Single();
        var raw = RawRepositorySnapshot.Create([
            new(BackfillInventoryLoader.RootPath + source.SourceId + "/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(source)),
            RawRepositoryEntry.FromText(PathFor(entry, State),
                Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan()) + (receipt ?? Receipt())),
        ]);
        return Assert.Single(BackfillInventoryLoader.Load(Decode(raw)).RequireDigestionEntries());
    }

    internal static RawRepositorySnapshot WithCas(AtomContextFixture fixture) =>
        RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Concat(
            fixture.Atomized.Claims.Select(atom => new RawRepositoryEntry(
                DigestionCasStore.RootPath + AtomContextFixture.Id(atom), atom.RawBytes))));
}
