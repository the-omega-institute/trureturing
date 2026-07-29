using StrataLint.Engine;

namespace StrataLint.Tests;

// Envelope / pre-committed-receipt / declaration-signature gates of the Phase 1
// cover transaction (spec §4a). Split out of CoverAtomTests.cs to keep that file
// under the SL-003 800-line artifact cap; kept as a partial of the same class so
// these tests reuse the shared CoverSpec/CoverWorld fixtures and the private
// Execute helper. The general cover gate matrix (CAS lock, arg parsing, scribe
// verifier, structural gates) stays in CoverAtomTests.cs.
public sealed partial class CoverAtomTests
{
    [Fact]
    public void CoverAcceptsBaseOwnedDeclarationWhenSignatureMatchesPreCommittedReceipt()
    {
        // Two-phase deposit: the covered declaration's Lean file was already landed
        // (and frozen) in PR-1, so at PR-2 the file is byte-identical to the base.
        // The old file-level newness gate false-rejected this ("is not new"),
        // forcing a fragile `--base <deposit-origin>` workaround. Gate ②(c) is now a
        // declaration-signature match against the pre-committed receipt, which is
        // base-agnostic: a base-owned declaration whose current signature equals the
        // pinned signature is admitted with an honest `--base baseline`.
        var (result, after, before) = Execute(new CoverSpec { BaselineTargetIdentical = true });

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.NotEqual(before, after);
        var entry = Assert.Single(
            BackfillInventoryLoader.Load(after).RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal(["D5/S0/Carrier/Probe.probe"], entry.CoverageGids.ToArray());
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
    }

    [Fact]
    public void CoverRejectsMissingEnvelopeReceipt()
    {
        // Fail-closed: without the pre-committed formalization receipt, cover cannot
        // confirm the deposited declaration matches a signature pinned before the
        // proof landed, so it refuses (no silent admission).
        var (result, after, before) = Execute(new CoverSpec { IncludeEnvelope = false });

        Assert.False(result.Success);
        Assert.Contains("receipt is missing", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsMalformedEnvelopeReceipt()
    {
        // Fail-closed: a receipt that is not canonical closed-schema JSON is refused.
        var (result, after, before) = Execute(new CoverSpec { MalformedEnvelope = true });

        Assert.False(result.Success);
        Assert.Contains("COVER_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsEnvelopePinnedForAnotherAtom()
    {
        // anti-Goodhart: a receipt pinned for atom A may not be used to cover a
        // different atom B — the receipt's atom_id must equal --cover-atom.
        var (result, after, before) = Execute(new CoverSpec { EnvelopeAtomId = "other-atom" });

        Assert.False(result.Success);
        Assert.Contains("atom_id other-atom does not match --cover-atom", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsEnvelopeWhosePrimaryGidDoesNotMatchCoverGid()
    {
        // The receipt pins a different primary declaration GID than the one being
        // covered: reject rather than bind the atom to an unpinned declaration.
        var (result, after, before) = Execute(new CoverSpec
        {
            EnvelopePrimaryGid = "D5/S0/Carrier/Probe.other",
        });

        Assert.False(result.Success);
        Assert.Contains("primary_gid", result.Error, StringComparison.Ordinal);
        Assert.Contains("does not match --gid", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsEnvelopeWhoseFingerprintDriftedFromAtom()
    {
        // The receipt's pinned content fingerprint no longer matches the atom's
        // fingerprint (the atom content drifted after the receipt was pinned).
        var (result, after, before) = Execute(new CoverSpec
        {
            EnvelopeCasRef = "sha256:" + new string('b', 64),
            EnvelopeRawSha256 = "sha256:" + new string('b', 64),
        });

        Assert.False(result.Success);
        Assert.Contains("fingerprint does not match atom", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRequiresTheEnvelopeArgument()
    {
        var spec = new CoverSpec();
        var (result, after, before) = Execute(
            spec,
            ["--cover-atom", spec.AtomId, "--gid", spec.Gid, "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("USAGE: StrataLint cover-atom", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    // §4(a) pre-committed signature match (implemented): a declaration whose
    // current signature diverges from the signature the formalizer pinned before
    // the proof landed is rejected. This is the machine guard against proving a
    // faithful statement and then swapping the theorem body (e.g. to `True`).
    [Fact]
    public void CoverRejectsFormalizationWhoseSignatureDoesNotMatchPreCommittedClaim()
    {
        // The receipt pins the real claim; the deposited declaration in the current
        // Lean report carries the hollow `True` body instead — signature mismatch.
        var (result, after, before) = Execute(new CoverSpec
        {
            PrecommittedSignature = new DigestionFormalizationSignature(
                "probe", "theorem", "2 + 2 = 4"),
        });

        Assert.False(result.Success);
        Assert.Contains("does not match the pre-committed signature", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    // §4(a) base-owned receipt (hardening): the pre-committed receipt is only
    // authoritative when it is part of the baseline (committed in PR-1). A same-PR
    // (spec A16 hostile-fork) attack that writes BOTH the declaration and a matching
    // receipt in one PR — so the receipt exists only in the candidate, never
    // pre-committed to the baseline — must be rejected. Otherwise the anti-swap
    // guard is forgeable in-PR (candidate-side "pre-commitment") and collapses.
    [Fact]
    public void CoverRejectsReceiptPresentOnlyInCandidateNotBaseline()
    {
        var (result, after, before) = Execute(new CoverSpec { EnvelopeInBaseline = false });

        Assert.False(result.Success);
        Assert.Contains("receipt is missing", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    // §4(a) base-owned receipt (hardening): a co-tampered same-PR swap. The honest
    // receipt in the baseline pins the real claim (`2 + 2 = 4`); the candidate
    // swaps the deposited declaration to the hollow `True` body AND overwrites the
    // candidate copy of the receipt to pin `True` so a candidate-side signature
    // match would pass. Base-owned load reads the baseline receipt, whose pinned
    // signature no longer matches the deposited `True` — the swap is caught. Before
    // the fix (candidate-side load) this deposit was admitted.
    [Fact]
    public void CoverUsesBaselineReceiptNotCandidateForSignatureMatch()
    {
        var (result, after, before) = Execute(new CoverSpec
        {
            BaselinePrecommittedSignature = new DigestionFormalizationSignature(
                "probe", "theorem", "2 + 2 = 4"),
        });

        Assert.False(result.Success);
        Assert.Contains("does not match the pre-committed signature", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    // §4(a) base-owned receipt (hardening): the legitimate two-phase deposit. The
    // receipt was committed in PR-1 and is part of the baseline; PR-2 covers with
    // the deposited declaration's current signature equal to the baseline-pinned
    // signature. Base-owned load reads the pre-committed baseline receipt and
    // admits the deposit.
    [Fact]
    public void CoverAcceptsWhenReceiptIsPreCommittedInBaselineAndSignatureMatches()
    {
        var (result, after, before) = Execute(new CoverSpec { EnvelopeInBaseline = true });

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.NotEqual(before, after);
        var entry = Assert.Single(
            BackfillInventoryLoader.Load(after).RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal(["D5/S0/Carrier/Probe.probe"], entry.CoverageGids.ToArray());
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
    }

    // §4(b) hollow-fidelity attestation is still deferred: signature-match proves
    // the deposited declaration equals what was pre-committed, but does NOT prove
    // the pre-committed signature itself is a faithful, non-hollow rendering of the
    // natural-language atom. A hollow pre-commitment (`theorem t : True`) deposited
    // unchanged would pass signature-match. Guarding the pre-commitment's fidelity
    // needs the separate digestion-fidelity-attestation-v1 / multi-model consensus
    // gate, which does not exist yet.
    [Fact(Skip = "Phase 2 §4(b): needs digestion-fidelity-attestation-v1 receipt "
        + "+ /sshx multi-model consensus attesting the pre-committed signature is "
        + "non-hollow; signature-match (§4a) is implemented and only proves "
        + "deposited == pre-committed")]
    public void CoverRejectsHollowTrueEmissionThatDischargesNothing()
    {
    }
}
