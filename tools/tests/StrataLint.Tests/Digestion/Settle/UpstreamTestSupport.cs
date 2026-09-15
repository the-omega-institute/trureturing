using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class UpstreamTestSupport
{
    internal const string Probe = "import Mathlib\nexample (a b : Nat) : a + b = b + a := Nat.add_comm a b\n";
    internal static string ProbePath(DigestionLedgerEntry entry) => "Meta/Digestion/upstream/" + entry.AtomId + ".lean";
    internal const string State = "upstream-closed";
    internal const string Reason = "Each clause follows from Nat.add_comm by normalization.";
    internal static string Receipt(string previous = "null", string next = "null") =>
        "  upstream:\n"
        + $"    justification: {Reason}\n"
        + "    declarations:\n      - Nat.add_comm\n"
        + $"    mathlib_rev: {new string('a', 40)}\n"
        + $"    probe_sha256: {DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(Probe)).RawSha256}\n"
        + "    probe_axioms: []\n"
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
        var source = DigestionTestSupport.Document(entry.Atomizer, [entry]).RequireDigestionSources().Single()
            with { SourceId = entry.SourceId, SourcePath = entry.SourcePath };
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
                DigestionCasStore.RootPath + AtomContextFixture.Id(atom), atom.RawBytes))).Concat(fixture.Ledger.RequireDigestionEntries().Select(entry =>
                    RawRepositoryEntry.FromText(ProbePath(entry), Probe))));
}
