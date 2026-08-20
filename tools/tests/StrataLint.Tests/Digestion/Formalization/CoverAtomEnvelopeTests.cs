using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
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
    public void CoverRejectsRepeatedGidsForTheInitialCoverOfAnOpenAtom()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryGid = secondaryModule + ".window_register_crt_decomposition";
        var spec = new CoverSpec
        {
            SecondaryTarget = (secondaryModule, "window_register_crt_decomposition"),
        };
        var inputs = spec.Materialize();

        var execution = Execute(
            spec,
            ["--cover-atom", spec.AtomId,
                "--gid", inputs.Gid,
                "--gid", secondaryGid,
                "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);
        var (result, after, before) = execution;

        Assert.False(result.Success);
        Assert.Contains("initial cover requires exactly one --gid", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsHostedExtensionWhenReceiptPrimaryIsNotAlreadyBound()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryDeclaration = "window_register_crt_decomposition";
        const string secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var spec = new CoverSpec
        {
            InitialCoverage = ImmutableArray.Create("D5/S0/Carrier/Probe.probe"),
            InitialDefinitionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256,
            InitialEmissionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256,
            Migration = "absorbed",
            Truth = "closed",
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
            EnvelopePrimaryGid = secondaryGid,
            PrecommittedSignature = new DigestionFormalizationSignature(
                secondaryDeclaration, "theorem", "True"),
        };
        var inputs = spec.Materialize();

        var execution = Execute(
            spec,
            ["--cover-atom", spec.AtomId,
                "--gid", inputs.Gid,
                "--gid", secondaryGid,
                "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);
        var (result, after, before) = execution;

        Assert.False(result.Success);
        Assert.Contains("primary_gid", result.Error, StringComparison.Ordinal);
        Assert.Contains("existing coverage", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverHostsArchivedWindowRegisterCrtAsASecondModuleUnderTheExistingReceipt()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryGid = secondaryModule + ".window_register_crt_decomposition";
        var spec = new CoverSpec
        {
            InitialCoverage = ImmutableArray.Create("D5/S0/Carrier/Probe.probe"),
            InitialDefinitionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256,
            InitialEmissionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256,
            Migration = "absorbed",
            Truth = "closed",
            SecondaryTarget = (secondaryModule, "window_register_crt_decomposition"),
        };
        var inputs = spec.Materialize();

        var execution = Execute(
            spec,
            ["--cover-atom", spec.AtomId,
                "--gid", inputs.Gid,
                "--gid", secondaryGid,
                "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);
        var (result, after, before) = execution;

        Assert.True(result.Success, result.Error);
        Assert.NotEqual(before, after);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal([inputs.Gid, secondaryGid], entry.CoverageGids.ToArray());
        Assert.Equal([inputs.Gid, secondaryGid],
            entry.Receipts.Coverage.Select(static receipt => receipt.Gid).ToArray());
        Assert.Equal([inputs.Gid, secondaryGid],
            entry.Receipts.Scribe.Select(static receipt => receipt.Gid).ToArray());
        Assert.Equal(DigestionMigrationState.Absorbed, entry.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
    }

    [Fact]
    public void CoverRejectsHostedExtensionWithoutABaseOwnedSecondarySignature()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryGid = secondaryModule + ".window_register_crt_decomposition";
        var spec = new CoverSpec
        {
            InitialCoverage = ImmutableArray.Create("D5/S0/Carrier/Probe.probe"),
            InitialDefinitionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256,
            InitialEmissionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256,
            Migration = "absorbed",
            Truth = "closed",
            SecondaryTarget = (secondaryModule, "window_register_crt_decomposition"),
            IncludeSecondaryPrecommittedSignature = false,
        };
        var inputs = spec.Materialize();

        var (result, after, before) = Execute(
            spec,
            ["--cover-atom", spec.AtomId,
                "--gid", inputs.Gid,
                "--gid", secondaryGid,
                "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        Assert.False(result.Success);
        Assert.Contains("base-owned pre-committed signature", result.Error, StringComparison.Ordinal);
        Assert.Contains(secondaryGid, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsHostedExtensionWhoseSecondarySignatureChangedAfterDeposit()
    {
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryDeclaration = "window_register_crt_decomposition";
        var secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var spec = new CoverSpec
        {
            InitialCoverage = ImmutableArray.Create("D5/S0/Carrier/Probe.probe"),
            InitialDefinitionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256,
            InitialEmissionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256,
            Migration = "absorbed",
            Truth = "closed",
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
            SecondaryPrecommittedSignature = new DigestionFormalizationSignature(
                secondaryDeclaration, "theorem", "2 + 2 = 4"),
        };
        var inputs = spec.Materialize();

        var (result, after, before) = Execute(
            spec,
            ["--cover-atom", spec.AtomId,
                "--gid", inputs.Gid,
                "--gid", secondaryGid,
                "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        Assert.False(result.Success);
        Assert.Contains("does not match the pre-committed signature", result.Error,
            StringComparison.Ordinal);
        Assert.Contains(secondaryGid, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverRejectsPreviouslyHostedExtensionWhoseSignatureChangedAfterDeposit()
    {
        const string primaryGid = "D5/S0/Carrier/Probe.probe";
        const string earlierGid = "D5/S0/Carrier/Probe.earlier";
        const string secondaryModule = "D5/S3/Observer/WindowRegisterCRT";
        const string secondaryDeclaration = "window_register_crt_decomposition";
        const string secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var spec = new CoverSpec
        {
            InitialCoverage = [primaryGid, earlierGid],
            Migration = "partial",
            Truth = "closed",
            ReportDeclarations = ["probe", "earlier"],
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
            AdditionalHostedExtensions =
            [
                new DigestionFormalizationExtension(
                    earlierGid,
                    new DigestionFormalizationSignature("earlier", "theorem", "False")),
            ],
        };
        var inputs = spec.Materialize();

        var (result, after, before) = Execute(
            spec,
            ["--cover-atom", spec.AtomId,
                "--gid", primaryGid,
                "--gid", secondaryGid,
                "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        Assert.False(result.Success);
        Assert.Contains("does not match the pre-committed signature", result.Error,
            StringComparison.Ordinal);
        Assert.Contains(earlierGid, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, after);
    }

    [Fact]
    public void CoverAddsB1ToALegacyPartialClosedReceiptHostWithoutClearingResiduals()
    {
        const string primaryModule = "D5/S3/Observer/WindowCharacter";
        const string primaryDeclaration = "window_algebra_has_no_character";
        const string secondaryModule = "D5/S3/Observer/ClassicalAnswerTableExclusion";
        const string secondaryDeclaration = "noncontextual_and_local_double_exclusion";
        const string residue = "noncontextual-and-local-double-exclusion-synthesis";
        var existingCoverage = ImmutableArray.Create(
            primaryModule + "." + primaryDeclaration,
            "D5/S3/QuantumBounds/CHSHWitness.bell_chsh_value",
            "D5/S3/QuantumBounds/CHSHWitness.bell_density_is_state",
            "D5/S3/QuantumBounds/CHSHWitness.bob_observables_are_valid",
            "D5/S3/QuantumBounds/CHSHWitness.lifted_observables_form_chsh_tuple",
            "D5/S3/QuantumBounds/CHSHWitness.chsh_operator_eq_lifted_chsh",
            "D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_abs_le_two",
            "D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_eq_two_exists",
            "D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_bound_is_exact");
        var spec = new CoverSpec
        {
            ModuleGid = primaryModule,
            Declaration = primaryDeclaration,
            InitialCoverage = existingCoverage,
            InitialUnresolvedSubitems = ImmutableArray.Create(residue),
            Migration = "partial",
            Truth = "closed",
            ReportDeclarations = ImmutableArray.Create(primaryDeclaration),
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
        };
        var inputs = spec.Materialize();
        var secondaryGid = secondaryModule + "." + secondaryDeclaration;

        var (result, before, after) = ExecuteDirectory(
            spec,
            ["--cover-atom", spec.AtomId,
                "--gid", inputs.Gid,
                "--gid", secondaryGid,
                "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        Assert.True(result.Success, result.Error);
        var beforeEntry = Assert.Single(
            before.RequireDigestionEntries(),
            candidate => candidate.AtomId == spec.AtomId);
        Assert.Equal(existingCoverage.ToArray(), beforeEntry.CoverageGids.ToArray());
        Assert.Empty(beforeEntry.Receipts.Coverage);
        Assert.Empty(beforeEntry.Receipts.Scribe);
        Assert.Equal([residue], beforeEntry.Receipts.UnresolvedSubitems.ToArray());
        var entry = Assert.Single(
            after.RequireDigestionEntries(),
            candidate => candidate.AtomId == spec.AtomId);
        Assert.Equal(existingCoverage.Add(secondaryGid).ToArray(), entry.CoverageGids.ToArray());
        Assert.Equal([secondaryGid], entry.Receipts.Coverage.Select(static receipt => receipt.Gid).ToArray());
        Assert.Equal([secondaryGid], entry.Receipts.Scribe.Select(static receipt => receipt.Gid).ToArray());
        Assert.Equal([residue], entry.Receipts.UnresolvedSubitems.ToArray());
        Assert.Equal(DigestionMigrationState.Partial, entry.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
    }

    [Fact]
    public void CoverAddsB2ToBothLegacyHostsOfTheSameResidual()
    {
        const string primaryModule = "D5/S3/Observer/MeasurementMarginal";
        const string primaryDeclaration = "copied_record_partial_trace_offDiagonal_eq_zero";
        const string secondaryModule = "D5/S3/Observer/FiniteForgettingCertificate";
        const string secondaryDeclaration = "finite_history_certificate";
        const string residue = "six-state-finite-certificates";
        var primaryGid = primaryModule + "." + primaryDeclaration;
        var secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var existingCoverage = ImmutableArray.Create(
            "D5/S3/DivergenceSupport/ZeroSupportDefect.dpi_defect_nonneg_zero_support",
            primaryModule + ".copied_record_partial_trace_eq_address_blocks",
            primaryGid,
            "D5/S3/Divergence/DpiDefect.dpi_defect_nonneg");
        var unresolvedSubitems = ImmutableArray.Create(
            "know-forgot-two-time-relation",
            residue,
            "joint-coherent-reversal-of-all-copies",
            "multi-copy-erasure-quantifier");
        var siblingUnresolvedSubitems = ImmutableArray.Create(
            "know-forgot-two-time-relation",
            residue,
            "v2-entropy-monotone-capacity-decrease",
            "v3-revival-spectrum-diophantine-grading",
            "multi-copy-erasure-quantifier");
        var spec = new CoverSpec
        {
            ModuleGid = primaryModule,
            Declaration = primaryDeclaration,
            InitialCoverage = existingCoverage,
            InitialUnresolvedSubitems = unresolvedSubitems,
            Migration = "partial",
            Truth = "closed",
            ReportDeclarations = ImmutableArray.Create(
                "copied_record_partial_trace_eq_address_blocks",
                primaryDeclaration),
            SecondaryTarget = (secondaryModule, secondaryDeclaration),
            HostedSibling = new CoverHostedSiblingSpec(
                "same-residual-host",
                primaryGid,
                existingCoverage.Add(secondaryGid),
                existingCoverage,
                siblingUnresolvedSubitems),
        };
        var inputs = spec.Materialize();

        var (result, before, after) = ExecuteDirectory(
            spec,
            ["--cover-atom", spec.AtomId,
                "--gid", primaryGid,
                "--gid", secondaryGid,
                "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        Assert.True(result.Success, result.Error);
        var beforeEntries = before.RequireDigestionEntries();
        var beforeTarget = Assert.Single(beforeEntries, candidate => candidate.AtomId == spec.AtomId);
        Assert.Equal(existingCoverage.ToArray(), beforeTarget.CoverageGids.ToArray());
        Assert.Empty(beforeTarget.Receipts.Coverage);
        Assert.Empty(beforeTarget.Receipts.Scribe);
        Assert.Equal(unresolvedSubitems.ToArray(), beforeTarget.Receipts.UnresolvedSubitems.ToArray());
        var beforeSibling = Assert.Single(
            beforeEntries,
            candidate => candidate.AtomId == "same-residual-host");
        Assert.Equal(
            existingCoverage.Add(secondaryGid).ToArray(),
            beforeSibling.CoverageGids.ToArray());
        Assert.Empty(beforeSibling.Receipts.Coverage);
        Assert.Empty(beforeSibling.Receipts.Scribe);
        Assert.Equal(
            siblingUnresolvedSubitems.ToArray(),
            beforeSibling.Receipts.UnresolvedSubitems.ToArray());
        var entries = after.RequireDigestionEntries();
        var target = Assert.Single(entries, candidate => candidate.AtomId == spec.AtomId);
        var sibling = Assert.Single(entries, candidate => candidate.AtomId == "same-residual-host");
        Assert.Equal(target.AstPath, sibling.AstPath);
        Assert.Equal(existingCoverage.Add(secondaryGid).ToArray(), target.CoverageGids.ToArray());
        Assert.Equal(existingCoverage.Add(secondaryGid).ToArray(), sibling.CoverageGids.ToArray());
        Assert.Equal(unresolvedSubitems.ToArray(), target.Receipts.UnresolvedSubitems.ToArray());
        Assert.Equal(
            siblingUnresolvedSubitems.ToArray(),
            sibling.Receipts.UnresolvedSubitems.ToArray());
        Assert.Equal(DigestionMigrationState.Partial, target.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, target.ProjectedStatus.Truth);
        Assert.Equal(DigestionMigrationState.Partial, sibling.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, sibling.ProjectedStatus.Truth);
    }

    [Fact]
    public void CoverRejectsSharedResidualHostWithoutAFullyMatchingBaseReceipt()
    {
        const string primaryModule = "D5/S3/Observer/MeasurementMarginal";
        const string primaryDeclaration = "copied_record_partial_trace_offDiagonal_eq_zero";
        const string secondaryModule = "D5/S3/Observer/FiniteForgettingCertificate";
        const string secondaryDeclaration = "finite_history_certificate";
        const string residue = "six-state-finite-certificates";
        var primaryGid = primaryModule + "." + primaryDeclaration;
        var secondaryGid = secondaryModule + "." + secondaryDeclaration;
        var canonicalSibling = new CoverHostedSiblingSpec(
            "same-residual-host",
            primaryGid,
            [primaryGid, secondaryGid],
            [primaryGid],
            [residue]);
        var cases = new (CoverHostedSiblingSpec Sibling, string Error)[]
        {
            (canonicalSibling with { IncludeReceipt = false }, "receipt is missing"),
            (canonicalSibling with { ReceiptAtomId = "wrong-host" }, "does not match atom"),
            (canonicalSibling with { ReceiptPrimaryGid = secondaryGid }, "does not match existing coverage"),
            (canonicalSibling with
            {
                ReceiptCasRef = "sha256:" + new string('a', 64),
            }, "fingerprint does not match atom"),
            (canonicalSibling with
            {
                ReceiptRawSha256 = "sha256:" + new string('b', 64),
            }, "fingerprint does not match atom"),
        };

        foreach (var (sibling, error) in cases)
        {
            var spec = new CoverSpec
            {
                ModuleGid = primaryModule,
                Declaration = primaryDeclaration,
                InitialCoverage = ImmutableArray.Create(primaryGid),
                InitialDefinitionSha256 = DigestionFingerprint.Compute(
                    Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256,
                InitialEmissionSha256 = DigestionFingerprint.Compute(
                    Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256,
                InitialUnresolvedSubitems = ImmutableArray.Create(residue),
                Migration = "partial",
                Truth = "closed",
                ReportDeclarations = ImmutableArray.Create(primaryDeclaration),
                SecondaryTarget = (secondaryModule, secondaryDeclaration),
                HostedSibling = sibling,
            };
            var inputs = spec.Materialize();

            var (result, after, before) = Execute(
                spec,
                ["--cover-atom", spec.AtomId,
                    "--gid", primaryGid,
                    "--gid", secondaryGid,
                    "--base", "baseline",
                    "--envelope", inputs.EnvelopePath]);

            Assert.False(result.Success);
            Assert.Contains(error, result.Error, StringComparison.Ordinal);
            Assert.Equal(before, after);
        }
    }

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
        var execution = Execute(new CoverSpec { BaselineTargetIdentical = true });
        var (result, after, before) = execution;

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.NotEqual(before, after);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal(["D5/S0/Carrier/Probe.probe"], entry.CoverageGids.ToArray());
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
    }

    [Fact]
    public void TrustedBaselineFormalizationReceiptCanonicalityIsNotReplayed()
    {
        var execution = Execute(new CoverSpec
        {
            BaselineTargetIdentical = true,
            NoncanonicalBaselineEnvelope = true,
        });
        var (result, after, before) = execution;

        Assert.True(result.Success, result.Error);
        Assert.NotEqual(before, after);
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
        var execution = Execute(new CoverSpec { EnvelopeInBaseline = true });
        var (result, after, before) = execution;

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.NotEqual(before, after);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
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

    private static (
        CommandResult Result,
        BackfillInventoryDocument Before,
        BackfillInventoryDocument After) ExecuteDirectory(
            CoverSpec spec,
            IReadOnlyList<string> arguments)
    {
        var inputs = spec.Materialize();
        var files = DirectoryLedgerTestSupport.Project(inputs.Files);
        var baseline = DirectoryLedgerTestSupport.Project(inputs.Baseline);
        var reportFiles = inputs.Report.Files.ToDictionary(
            static pair => pair.Key.Value,
            static pair => pair.Value,
            StringComparer.Ordinal);
        MaterializeExistingCoverageTargets(spec, files, reportFiles);
        MaterializeExistingCoverageTargets(spec, baseline, reportFiles);
        var directoryInputs = inputs with
        {
            Files = files,
            Baseline = baseline,
            Report = LeanAxiomReport.Create(reportFiles),
        };
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, directoryInputs.Files);
        var before = BackfillInventoryLoader.LoadRoot(temporary.Path);

        var result = CoverWorld.Environment(
            temporary.Path,
            directoryInputs,
            directoryInputs.Files).CoverAtom(arguments);

        return (result, before, BackfillInventoryLoader.LoadRoot(temporary.Path));
    }

    private static void MaterializeExistingCoverageTargets(
        CoverSpec spec,
        IDictionary<string, string> files,
        IDictionary<string, LeanFileReport> reportFiles)
    {
        var coverage = spec.InitialCoverage
            .Concat(spec.HostedSibling?.CurrentCoverage ?? [])
            .Concat(spec.HostedSibling?.BaselineCoverage ?? []);
        foreach (var gidText in coverage)
        {
            var gid = Assert.IsType<Gid>(Gid.TryParse(gidText, out var parsed) ? parsed : null);
            var moduleGid = gid.Path.Value[..^".lean".Length];
            files.TryAdd(gid.Path.Value, DigestionTestSupport.Lean(moduleGid));
            var declarationName = gidText[(gidText.LastIndexOf('.') + 1)..];
            if (!reportFiles.TryGetValue(gid.Path.Value, out var fileReport))
            {
                reportFiles.Add(
                    gid.Path.Value,
                    new LeanFileReport(
                        [],
                        [new LeanDeclaration(declarationName, "theorem", "True", [])]));
            }
            else if (!fileReport.Declarations.Any(declaration =>
                         string.Equals(declaration.Name, declarationName, StringComparison.Ordinal)))
            {
                reportFiles[gid.Path.Value] = fileReport with
                {
                    Declarations = fileReport.Declarations.Add(
                        new LeanDeclaration(declarationName, "theorem", "True", [])),
                };
            }
        }
    }
}

internal static partial class CoverWorld
{
    private static List<ScribeEmissionRecord> MaterializeScribeRecords(
        CoverSpec spec,
        ScribeEmissionRecord primary)
    {
        var records = new List<ScribeEmissionRecord> { primary };
        if (spec.SecondaryTarget is { } secondary)
        {
            var definition = Encoding.UTF8.GetBytes("secondary scribe definition\n");
            var emission = Encoding.UTF8.GetBytes("# secondary emitted narrative\n");
            records.Add(new ScribeEmissionRecord(
                secondary.ModuleGid,
                ScribeEmissionAttestation.DefinitionPath(secondary.ModuleGid),
                DigestionFingerprint.Compute(definition).RawSha256,
                ScribeEmissionAttestation.EmissionPath(secondary.ModuleGid),
                DigestionFingerprint.Compute(emission).RawSha256));
        }

        return records;
    }

    private static void MaterializeSecondaryFiles(CoverSpec spec, IDictionary<string, string> files)
    {
        if (spec.SecondaryTarget is not { } secondary)
        {
            return;
        }

        files[secondary.ModuleGid + ".lean"] = DigestionTestSupport.Lean(secondary.ModuleGid);
        files[ScribeEmissionAttestation.DefinitionPath(secondary.ModuleGid)] =
            "secondary scribe definition\n";
        files[ScribeEmissionAttestation.EmissionPath(secondary.ModuleGid)] =
            "# secondary emitted narrative\n";
    }

    private static LeanAxiomReport MaterializeReport(
        CoverSpec spec,
        string targetPath,
        ImmutableArray<LeanDeclaration> primaryDeclarations)
    {
        var reportFiles = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [targetPath] = new LeanFileReport(ImmutableArray<string>.Empty, primaryDeclarations),
        };
        if (spec.SecondaryTarget is { } secondary)
        {
            reportFiles[secondary.ModuleGid + ".lean"] = new LeanFileReport(
                ImmutableArray<string>.Empty,
                [new LeanDeclaration(
                    secondary.Declaration,
                    "theorem",
                    "True",
                    ImmutableArray<string>.Empty)]);
        }

        return LeanAxiomReport.Create(reportFiles);
    }

    private static IEnumerable<string> MaterializeVerifiedGids(CoverSpec spec) =>
        (spec.Declaration is null ? [] : new[] { spec.Gid })
            .Concat(spec.SecondaryTarget is { } secondary
                ? [secondary.ModuleGid + "." + secondary.Declaration]
                : []);
}
