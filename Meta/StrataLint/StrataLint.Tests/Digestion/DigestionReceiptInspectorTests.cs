using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed class DigestionReceiptInspectorTests
{
    [Fact]
    public void InspectorReturnsLocalCompletenessAndProgressFacts()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source).Claims);
        var target = Encoding.UTF8.GetBytes(Lean("D5/S0/Carrier/Probe"));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var entry = EntryWithReceipts(atom, target, definition, emission);
        var targetPath = RepoPath.CreateKnown("D5/S0/Carrier/Probe.lean");
        var findings = ImmutableArray.CreateBuilder<string>();

        var inspection = DigestionReceiptInspector.Inspect(
            entry,
            DigestionReceiptAlignment.Seen,
            baselineEntry: null,
            Snapshot(
                ("docs/source.md", source),
                CasFile(atom),
                (targetPath.Value, target),
                ("Blueprint/D5/S0/Carrier/Probe.scribe.cs", definition),
                ("Blueprint/D5/S0/Carrier/Probe.md", emission)),
            AcceptedLean(targetPath.Value).Report,
            new Dictionary<RepoPath, TruthNode>
            {
                [targetPath] = TruthNode.Create(targetPath, gid: null, TruthState.Closed, "D5.S0.Carrier.Probe"),
            },
            ScribeEmissionAttestation.Empty,
            verifiedScribeEmissions: null,
            findings);

        Assert.False(inspection.LocalComplete);
        Assert.True(inspection.HasProgress);
        var targetState = Assert.Single(inspection.TargetStates);
        Assert.Equal("D5/S0/Carrier/Probe", targetState.Gid);
        Assert.Equal(TruthState.Closed, targetState.State);
        Assert.Contains(inspection.Gaps, gap => gap.Code == "scribe-attestation-missing");
        Assert.Contains(inspection.Gaps, gap => gap.Code == "scribe-emission-unverified");
        Assert.Empty(findings);
    }

    private static DigestionLedgerEntry EntryWithReceipts(
        DigestionAtom atom,
        byte[] target,
        byte[] definition,
        byte[] emission) =>
        new(
            AtomizerRegistry.GictId,
            "docs/source.md",
            AtomizerRegistry.GictId,
            "gict-1.1",
            atom.AstPath,
            new DigestionBoundary(atom.AstPath, atom.StartByte, atom.EndByte),
            atom.Fingerprints,
            ["D5/S0/Carrier/Probe"],
            new DigestionReceipts(
                [
                    new DigestionCoverageReceipt(
                        "D5/S0/Carrier/Probe",
                        atom.Fingerprints.RawSha256,
                        DigestionFingerprint.Compute(target).RawSha256),
                ],
                [
                    new DigestionScribeReceipt(
                        "D5/S0/Carrier/Probe",
                        DigestionFingerprint.Compute(definition).RawSha256,
                        DigestionFingerprint.Compute(emission).RawSha256),
                ],
                [],
                [],
                TailAuthorization: null),
            new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            ReceiptSyntax: null,
            atom.Fingerprints.RawSha256);
}
