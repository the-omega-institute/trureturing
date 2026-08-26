using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void IngestQualifiesAByteIdenticalResidualWhenTheLegacyContentIdIsAlreadyInTheLedger()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\n| κ | 1 |\n");
        var atoms = GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules).Claims;
        Assert.Equal(2, atoms.Length);
        Assert.Equal(atoms[0].RawBytes.ToArray(), atoms[1].RawBytes.ToArray());
        Assert.InRange(atoms[0].RawBytes.Length, 1, 16);
        var captured = DigestionCasStore.Capture(atoms[0].RawBytes.AsSpan());
        var legacyAtomId = ResidualStem(atoms[0]);
        var ledger = Ledger(
            [],
            CasEntry(legacyAtomId, atoms[0], captured.Reference));

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [captured]),
            ledger);

        var entries = plan.Document.RequireDigestionEntries();
        Assert.Equal(2, entries.Length);
        Assert.Contains(entries, entry =>
            entry.AtomId == legacyAtomId && entry.AstPath == atoms[0].AstPath);
        var occurrence = Assert.Single(entries, entry => entry.AstPath == atoms[1].AstPath);
        Assert.Equal(OccurrenceAtomId(atoms[1]), occurrence.AtomId);
        Assert.Equal(captured.Reference, occurrence.CasRef);
        Assert.Single(plan.CasObjects);
    }

    [Fact]
    public void IngestQualifiesAGenericResidualWhenItsLegacyStemIsAlreadyInTheLedger()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# 定理 1.1\n\n证。\n");
        var atom = Assert.Single(GenericAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var legacyAtomId = GenericResidualStem(atom);
        var ledger = WithAtomizer(Ledger(
            [],
            CasEntry(legacyAtomId, atom, captured.Reference) with
            {
                AstPath = "section/old-locator",
            }),
            AtomizerRegistry.GenericId);

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [captured]),
            ledger);

        var entries = plan.Document.RequireDigestionEntries();
        Assert.Equal(2, entries.Length);
        Assert.Contains(entries, entry =>
            entry.AtomId == legacyAtomId && entry.AstPath == "section/old-locator");
        var residual = Assert.Single(entries, entry => entry.AstPath == atom.AstPath);
        Assert.Equal(legacyAtomId + "-" + OccurrenceSuffix(atom), residual.AtomId);
        Assert.Equal(captured.Reference, residual.CasRef);
    }

    [Fact]
    public void IngestRejectsWhenTheDeterministicOccurrenceIdIsAlreadyInTheLedger()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\n| κ | 1 |\n\n"
            + "**定理 1.1(A)**。blocker。\n");
        var atoms = GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules).Claims;
        var repeated = atoms
            .GroupBy(static atom => atom.Fingerprints.RawSha256, StringComparer.Ordinal)
            .Single(static group => group.Count() == 2)
            .ToArray();
        var blocker = atoms.Single(atom =>
            atom.Fingerprints.RawSha256 != repeated[0].Fingerprints.RawSha256);
        var repeatedCapture = DigestionCasStore.Capture(repeated[0].RawBytes.AsSpan());
        var blockerCapture = DigestionCasStore.Capture(blocker.RawBytes.AsSpan());
        var occurrenceAtomId = OccurrenceAtomId(repeated[1]);
        var ledger = Ledger(
            [],
            CasEntry(ResidualStem(repeated[0]), repeated[0], repeatedCapture.Reference),
            CasEntry(occurrenceAtomId, blocker, blockerCapture.Reference));

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [repeatedCapture, blockerCapture]),
            ledger));

        Assert.Contains(
            $"ingest residual atom_id collides with the ledger: {occurrenceAtomId}",
            exception.Message,
            StringComparison.Ordinal);
    }

    private static string ResidualStem(DigestionAtom atom) =>
        AtomizerRegistry.Require(AtomizerRegistry.GictId).ResidualPrefix
        + "-residual-"
        + atom.Fingerprints.RawSha256["sha256:".Length..];

    private static string GenericResidualStem(DigestionAtom atom) =>
        AtomizerRegistry.Require(AtomizerRegistry.GenericId).ResidualPrefix
        + "-residual-"
        + atom.Fingerprints.RawSha256["sha256:".Length..];

    private static string OccurrenceAtomId(DigestionAtom atom) =>
        ResidualStem(atom) + "-" + OccurrenceSuffix(atom);

    private static string OccurrenceSuffix(DigestionAtom atom) =>
        Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(
            Encoding.UTF8.GetBytes("source\0" + atom.AstPath)));
}
