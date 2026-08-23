using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

// Phase 1 cover transaction: bind one or more already-proven Lean declarations to an
// existing open residual atom by writing coverage_gids + coverage/scribe
// receipts. cover is the narrow sibling of ingest — it reuses
// DigestionStatusEvaluator for the structural gates and never adds residual
// atoms or rebinds boundaries. The write is all-or-nothing with a fail-closed
// check-then-act guard: every gate must pass and the on-disk ledger must still
// exist and be unchanged before ReplaceLedgerAtomically touches disk, otherwise
// BACKFILL.yaml is byte-unchanged. This is not a true CAS/lock — a residual
// sub-millisecond TOCTOU window remains between the reread and the atomic rename
// (serialized manual/CI invocation makes it sufficient; an OS file lock for a
// hard guarantee is deferred).
//
// Gate ②(c) (§4a, implemented): cover pins the deposit against a pre-committed
// digestion-formalization-v1 receipt supplied by --envelope. The receipt is loaded
// from the BASELINE snapshot (repository.ReadRevision(--base)), never the candidate,
// so "pre-committed" is a machine invariant rather than an honesty convention: the
// receipt must already be committed to the baseline (PR-1 of the two-phase flow),
// and a candidate PR cannot fabricate or alter the receipt it is judged against from
// inside its own diff. Under the admission gate --base is the pull_request_target-
// fixed baseline (dev), so a receipt introduced by the candidate is not yet in the
// baseline and the deposit is rejected. The receipt binds atom_id + primary_gid +
// the atom's content fingerprint (cas_ref/raw_sha256), and the deposited
// declaration's *current* signature (name_key/kind/type, read from the candidate raw
// Lean report) must equal the signature the formalizer pinned in the base-owned
// receipt before the proof landed. This replaces the old file-level newness
// heuristic: no declaration file bytes are compared, so the honest two-phase deposit
// (declaration frozen/base-owned in PR-1) is still accepted, while a post-proof
// statement swap is machine-rejected because the deposited signature then diverges
// from the base-owned pinned signature — even if the attacker co-tampers the
// candidate copy of the receipt in the same PR (the co-tampered copy is not read).
//
// Deferred (recorded, not silent):
//  - Hollow-fidelity attestation (§4b): signature-match proves deposited ==
//    pre-committed, but not that the pre-committed signature is itself a faithful,
//    non-hollow rendering of the natural-language atom. base-ownership does NOT close
//    this: a hollow pre-commitment landed in PR-1 (both the `theorem t : True`
//    declaration and its matching receipt base-owned) then deposited unchanged still
//    passes signature-match. That needs the separate digestion-fidelity-
//    attestation-v1 receipt + /sshx multi-model consensus.
//  - Receipt emission + residence: the formalizer/workflow (step 1) is responsible
//    for producing and committing the receipt at a digestion data path; this
//    command only consumes it. Receipt lifecycle (deletion after absorption) is a
//    workflow concern.
//  - kind exclusion gate (spec §5): a producer responsibility, not cover's.
internal static partial class CoverAtomCommand
{
    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var options = ParseArguments(arguments);
            var currentRaw = repository.ReadCurrent();
            var baselineRaw = repository.ReadRevision(options.BaselineRevision);
            var current = Decode(currentRaw);
            var baseline = Decode(baselineRaw);
            var document = LoadDocument(current);
            var baselineDocument = BackfillInventoryLoader.LoadBaseline(baseline);

            // Gate ②(a): every cover GID must select a Lean declaration, not just a
            // module (module-level coverage is ingest's residual boundary, not a
            // single truth atom).
            var gids = options.Gids.Select(gidText =>
            {
                if (!Gid.TryParse(gidText, out var gid)
                    || gid.ToTarget() is not Target.Formal { Declaration: not null })
                {
                    throw new InvalidOperationException(
                        $"cover GID must select a Lean declaration: {gidText}");
                }

                return gid;
            }).ToImmutableArray();

            // Gate ①: locate the single target atom. An initial cover requires an
            // open atom; a hosted extension adds at least one declaration while
            // retaining all existing coverage.
            var sources = document.RequireDigestionSources();
            var target = LocateTarget(sources, options.AtomId, options.Gids);
            var existingGids = target.CoverageGids.ToImmutableHashSet(StringComparer.Ordinal);
            var addedGids = options.Gids.Where(gid => !existingGids.Contains(gid)).ToImmutableArray();
            var report = leanReportSource.Load(current);
            var lean = ValidateLean(current, report);
            var verifiedScribeEmissions = scribeEmissionVerifier.Verify(current, report);
            var beforeEvaluation = DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.FullScan,
                document,
                current,
                lean,
                verifiedScribeEmissions,
                baselineDocument,
                baselineSnapshot: baseline);
            RequireNoFindings(beforeEvaluation);

            // Gate ②(b): anti-Goodhart — cover may only deposit a declaration that
            // the baseline ledger did not already bind.
            var baselineGids = BaselineCoverageGids(baselineDocument);
            if (addedGids.FirstOrDefault(baselineGids.Contains) is { } baselineConflict)
            {
                throw new InvalidOperationException(
                    $"cover GID {baselineConflict} is already bound in the baseline ledger");
            }

            // Gate ⑤: the old unique GID -> atom rejection remains unchanged except
            // for legacy duplicate hosts of the same residual. That narrow path is
            // available only when both atoms have base-owned, fully validated v1
            // receipts whose primary GIDs are already bound.
            foreach (var gidText in options.Gids)
            {
                foreach (var conflict in FindCrossAtomBindings(sources, options.AtomId, gidText))
                {
                    RequireSharedResidualHost(
                        target,
                        conflict,
                        baselineDocument,
                        baseline,
                        report,
                        gidText);
                }
            }

            var addedReceipts = gids
                .Where(gid => !existingGids.Contains(gid.Value))
                .Select(gid => BuildReceipts(
                    target,
                    gid,
                    current,
                    verifiedScribeEmissions))
                .ToImmutableArray();
            var covered = target with
            {
                CoverageGids = target.CoverageGids.AddRange(addedGids),
                Receipts = target.Receipts with
                {
                    Coverage = target.Receipts.Coverage.AddRange(
                        addedReceipts.Select(static receipt => receipt.Coverage)),
                    Scribe = target.Receipts.Scribe.AddRange(
                        addedReceipts.Select(static receipt => receipt.Scribe)),
                },
            };
            var plannedDocument = ReplaceEntry(document, options.AtomId, covered);

            var derived = DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.FullScan,
                plannedDocument,
                current,
                lean,
                verifiedScribeEmissions,
                baselineDocument,
                validateProjectedStatus: false,
                baselineSnapshot: baseline);
            RequireNoFindings(derived);

            var statusByAtomId = derived.Entries.ToDictionary(
                static item => item.Entry.AtomId,
                static item => item.DerivedStatus,
                StringComparer.Ordinal);
            var refreshed = plannedDocument.WithDigestionSources(
                plannedDocument.RequireDigestionSources()
                    .Select(source => source with
                    {
                        Entries = source.Entries
                            .Select(entry => entry with
                            {
                                ProjectedStatus = statusByAtomId[entry.AtomId],
                            })
                            .ToImmutableArray(),
                    })
                    .ToImmutableArray());

            var finalRaw = IngestCommand.ReplaceLedger(
                currentRaw,
                document,
                refreshed);
            var finalSnapshot = Decode(finalRaw);
            var finalDocument = LoadDocument(finalSnapshot);
            var evaluation = DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.FullScan,
                finalDocument,
                finalSnapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument,
                baselineSnapshot: baseline);
            RequireNoFindings(evaluation);
            var backfillObservations = DigestionBackfillValidation.RequireValidBackfill(
                finalDocument,
                finalSnapshot,
                baseline,
                LoadPolicy(finalSnapshot),
                lean,
                verifiedScribeEmissions);

            var finalTarget = EvaluationFor(evaluation, options.AtomId);
            if (target.CoverageGids.Length == 0)
            {
                // Initial cover keeps the old semantics exactly: the atom must become
                // deletable Closed with no residual gap.
                RequireClosedDeletable(finalTarget);
            }
            else
            {
                // A validated receipt host may append Closed declarations without
                // pretending that its remaining semantic residuals were discharged.
                // Its migration/truth projection and gap set may only stay equal or
                // improve.
                RequireHostedExtension(
                    EvaluationFor(beforeEvaluation, options.AtomId),
                    finalTarget,
                    addedGids,
                    finalSnapshot,
                    lean);
            }

            var receipt = DigestionFormalizationReceipt.LoadTrusted(baseline, options.EnvelopePath);
            RequireEnvelopeBinding(receipt, options, target);
            RequireSignatureMatch(
                receipt,
                gids.Single(gid => string.Equals(gid.Value, receipt.PrimaryGid, StringComparison.Ordinal)),
                report);
            var hostedGids = target.CoverageGids.Length == 0
                ? []
                : receipt.HostedExtensions
                    .Select(static extension => extension.Gid)
                    .Concat(addedGids)
                    .Distinct(StringComparer.Ordinal);
            foreach (var hostedGid in hostedGids)
            {
                RequireHostedExtensionSignature(receipt, hostedGid, report);
            }

            // Gate ②(c): base-owned pre-committed formalization receipt +
            // declaration-signature match (spec §4a). Replaces the old file-level
            // newness gate. The receipt is loaded from the BASELINE snapshot, so the
            // anti-swap property is now a machine invariant rather than honesty-only:
            // the formalizer pins the atom's primary declaration signature
            // (name_key/kind/type) in a receipt committed to the baseline (PR-1)
            // before the proof lands; cover admits the declaration only when its
            // *current* signature in the candidate raw Lean report equals the
            // base-owned pinned signature. No file-byte comparison is made, so the
            // honest two-phase deposit (freeze in PR-1, cover in PR-2 with --base the
            // fixed baseline) is accepted, while a post-proof statement swap (e.g. to
            // `True`) is machine-rejected because the deposited signature diverges
            // from the base-owned pin — and, crucially, the candidate cannot launder
            // the swap by co-forging its own copy of the receipt in the same PR, since
            // the co-tampered candidate copy is never read (only the baseline receipt
            // is). The receipt also binds atom_id + primary_gid + the atom's content
            // fingerprint, so a receipt pinned for one atom cannot cover another
            // (anti-Goodhart).
            //
            // Deferred (§4b, recorded not silent): base-ownership closes the same-PR
            // fabrication/swap, but does NOT attest that the pre-committed signature is
            // itself a faithful, non-hollow rendering of the natural-language atom. A
            // hollow pre-commitment landed together in PR-1 (both the `True`
            // declaration and its matching receipt base-owned) then deposited unchanged
            // still passes signature-match. That is the separate
            // digestion-fidelity-attestation-v1 / multi-model consensus gate, out of
            // scope for this block.
            var ledgerUpdates = IngestCommand.LedgerUpdates(currentRaw, finalRaw);
            var changed = ledgerUpdates.Length > 0;
            IngestCommand.ApplyLedgerUpdatesAtomically(repositoryRoot, currentRaw, ledgerUpdates);

            return new CommandResult(
                true,
                $"COVER atom_id={options.AtomId} gid={string.Join(',', options.Gids)} "
                + $"ledger_changed={changed.ToString().ToLowerInvariant()}\n"
                + backfillObservations
                + DigestStatusCommand.RenderText(evaluation),
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"COVER_INVALID {exception.Message}\n");
        }
    }

    private static DigestionLedgerEntry LocateTarget(
        ImmutableArray<DigestionLedgerSource> sources,
        string atomId,
        ImmutableArray<string> requestedGids)
    {
        var matches = sources
            .SelectMany(static source => source.Entries)
            .Where(entry => string.Equals(entry.AtomId, atomId, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length == 0)
        {
            throw new InvalidOperationException($"cover atom {atomId} is absent from the ledger");
        }

        if (matches.Length > 1)
        {
            throw new InvalidOperationException($"cover atom {atomId} is ambiguous in the ledger");
        }

        var entry = matches[0];
        if (entry.CoverageGids.Length == 0 && requestedGids.Length != 1)
        {
            throw new InvalidOperationException(
                $"initial cover requires exactly one --gid for open atom {atomId}");
        }

        if (entry.CoverageGids.Length == 0
            && entry.ProjectedStatus.Truth != DigestionTruthState.Open)
        {
            throw new InvalidOperationException(
                $"cover atom {atomId} is not open "
                + $"(truth={DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)})");
        }

        var existing = entry.CoverageGids.ToImmutableHashSet(StringComparer.Ordinal);
        if (entry.CoverageGids.Length > 0 && requestedGids.All(existing.Contains))
        {
            throw new InvalidOperationException(
                $"cover atom {atomId} already has coverage: "
                + string.Join(", ", entry.CoverageGids));
        }

        return entry;
    }

    private static ImmutableHashSet<string> BaselineCoverageGids(
        BackfillInventoryDocument baselineDocument) =>
        baselineDocument.RequireDigestionEntries()
            .SelectMany(static entry => entry.CoverageGids)
            .ToImmutableHashSet(StringComparer.Ordinal);

    private static (DigestionCoverageReceipt Coverage, DigestionScribeReceipt Scribe) BuildReceipts(
        DigestionLedgerEntry entry,
        Gid gid,
        RepositorySnapshot snapshot,
        VerifiedScribeEmissions verifiedScribeEmissions)
    {
        if (!snapshot.TryGetFile(gid.Path.Value, out var target))
        {
            throw new InvalidOperationException($"cover target Lean file is absent: {gid.Path.Value}");
        }

        var documentGid = ScribeEmissionAttestation.DocumentGid(gid.Value);
        if (!verifiedScribeEmissions.TryGet(documentGid, out var verifiedRecord))
        {
            throw new InvalidOperationException(
                $"cover verified Scribe emission is absent: {documentGid} "
                + "(scribe-emission-missing; partial-closed)");
        }

        var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
        if (!snapshot.TryGetFile(definitionPath, out var definition))
        {
            throw new InvalidOperationException($"cover Scribe definition is absent: {definitionPath}");
        }

        var coverage = new DigestionCoverageReceipt(
            gid.Value,
            entry.Fingerprints.RawSha256,
            DigestionFingerprint.Compute(target.RawBytes.AsSpan()).RawSha256);
        var scribe = new DigestionScribeReceipt(
            gid.Value,
            DigestionFingerprint.Compute(definition.RawBytes.AsSpan()).RawSha256,
            verifiedRecord.EmissionSha256);
        return (coverage, scribe);
    }

    private static BackfillInventoryDocument ReplaceEntry(
        BackfillInventoryDocument document,
        string atomId,
        DigestionLedgerEntry covered) =>
        document.WithDigestionSources(
            document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries
                        .Select(entry => string.Equals(entry.AtomId, atomId, StringComparison.Ordinal)
                            ? covered
                            : entry)
                        .ToImmutableArray(),
                })
                .ToImmutableArray());

    private static DigestionEntryEvaluation EvaluationFor(
        DigestionLedgerEvaluation evaluation,
        string atomId) =>
        evaluation.Entries.Single(entry =>
            string.Equals(entry.Entry.AtomId, atomId, StringComparison.Ordinal));

    private static void RequireClosedDeletable(DigestionEntryEvaluation covered)
    {
        if (covered.Deletable && covered.DerivedStatus.Truth == DigestionTruthState.Closed)
        {
            return;
        }

        throw new InvalidOperationException(
            $"cover atom {covered.Entry.AtomId} did not reach a deletable Closed state: "
            + $"{DigestionStatusNames.Migration(covered.DerivedStatus.Migration)}-"
            + $"{DigestionStatusNames.Truth(covered.DerivedStatus.Truth)} "
            + $"deletable={covered.Deletable.ToString().ToLowerInvariant()} "
            + $"gaps={string.Join(",", covered.Gaps.Select(static gap => gap.Code))}");
    }

    private static void RequireEnvelopeBinding(
        DigestionFormalizationReceipt receipt,
        CoverArguments options,
        DigestionLedgerEntry target)
    {
        if (!string.Equals(receipt.AtomId, options.AtomId, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"cover envelope atom_id {receipt.AtomId} does not match --cover-atom {options.AtomId}");
        }

        if (target.CoverageGids.Length > 0
            && !target.CoverageGids.Contains(receipt.PrimaryGid, StringComparer.Ordinal))
        {
            throw new InvalidOperationException(
                $"cover envelope primary_gid {receipt.PrimaryGid} does not match existing coverage "
                + $"for atom {options.AtomId}");
        }

        if (!options.Gids.Contains(receipt.PrimaryGid, StringComparer.Ordinal))
        {
            throw new InvalidOperationException(
                $"cover envelope primary_gid {receipt.PrimaryGid} does not match --gid values");
        }

        if (!string.Equals(receipt.CasRef, target.Fingerprints.RawSha256, StringComparison.Ordinal)
            || !string.Equals(receipt.RawSha256, target.Fingerprints.RawSha256, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"cover envelope fingerprint does not match atom {options.AtomId} "
                + $"(atom raw {target.Fingerprints.RawSha256})");
        }
    }

    private static void RequireSignatureMatch(
        DigestionFormalizationReceipt receipt,
        Gid gid,
        LeanAxiomReport report) =>
        RequireSignatureMatch(gid, report, receipt.Signature);

    private static void RequireHostedExtensionSignature(
        DigestionFormalizationReceipt receipt,
        string gidText,
        LeanAxiomReport report)
    {
        var matches = receipt.HostedExtensions
            .Where(extension => string.Equals(extension.Gid, gidText, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length != 1)
        {
            throw new InvalidOperationException(
                $"cover hosted extension {gidText} has no base-owned pre-committed signature");
        }

        if (!Gid.TryParse(gidText, out var gid))
        {
            throw new InvalidOperationException(
                $"cover hosted extension GID is invalid: {gidText}");
        }

        RequireSignatureMatch(gid, report, matches[0].Signature);
    }

    private static void RequireSignatureMatch(
        Gid gid,
        LeanAxiomReport report,
        DigestionFormalizationSignature pinned)
    {
        // By the time this runs the Closed-deletable gate has already established the
        // declaration exists and is unique, so ResolveSignature is expected to
        // succeed; its fail-closed throw remains a defensive invariant guard.
        var deposited = DigestionFormalizationReceipt.ResolveSignature(gid, report);
        if (deposited != pinned)
        {
            throw new InvalidOperationException(
                $"cover declaration {gid.Value} signature "
                + $"({deposited.NameKey}, {deposited.Kind}, {deposited.Type}) "
                + "does not match the pre-committed signature "
                + $"({pinned.NameKey}, {pinned.Kind}, {pinned.Type})");
        }
    }

    private sealed record CoverArguments(
        string AtomId,
        ImmutableArray<string> Gids,
        string BaselineRevision,
        string EnvelopePath);

    private sealed record AlignArguments(string AtomId, string Gid);

    private static CoverArguments ParseArguments(IReadOnlyList<string> arguments)
    {
        string? atomId = null;
        var gids = ImmutableArray.CreateBuilder<string>();
        string? baselineRevision = null;
        string? envelopePath = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count)
            {
                throw Usage();
            }

            switch (arguments[index])
            {
                case "--cover-atom" when atomId is null:
                    atomId = arguments[index + 1];
                    break;
                case "--gid":
                    gids.Add(arguments[index + 1]);
                    break;
                case "--base" when baselineRevision is null:
                    baselineRevision = arguments[index + 1];
                    break;
                case "--envelope" when envelopePath is null:
                    envelopePath = arguments[index + 1];
                    break;
                default:
                    throw Usage();
            }
        }

        if (string.IsNullOrWhiteSpace(atomId)
            || gids.Count == 0
            || gids.Any(string.IsNullOrWhiteSpace)
            || gids.Distinct(StringComparer.Ordinal).Count() != gids.Count
            || string.IsNullOrWhiteSpace(baselineRevision)
            || string.IsNullOrWhiteSpace(envelopePath))
        {
            throw Usage();
        }

        return new CoverArguments(atomId, gids.ToImmutable(), baselineRevision, envelopePath);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint cover-atom --cover-atom ATOM_ID --gid DECL_GID [--gid DECL_GID ...] --base REV "
        + "--envelope RECEIPT_PATH");

    private static BackfillInventoryDocument LoadDocument(RepositorySnapshot snapshot) =>
        BackfillInventoryLoader.Load(snapshot);

    private static void RequireNoFindings(DigestionLedgerEvaluation evaluation)
    {
        if (evaluation.HasReceiptIntegrityFailure)
        {
            var gaps = evaluation.Entries.SelectMany(static entry => entry.Gaps.Select(gap =>
                $"atom={entry.Entry.AtomId} code={gap.Code} detail={gap.Detail}"));
            throw new InvalidOperationException(
                "digest status is invalid: " + string.Join("; ", evaluation.Findings.Concat(gaps)));
        }
    }

    private static ValidatedPolicy LoadPolicy(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile("Meta/registry.yaml", out var registry)
            || !snapshot.TryGetFile("Meta/domains.yaml", out var domains))
        {
            throw new InvalidOperationException(
                "cover requires Meta/registry.yaml and Meta/domains.yaml");
        }

        return RegistryLoader.Load(registry.RawBytes.AsSpan(), domains.RawBytes.AsSpan()) switch
        {
            RegistryLoadOutcome.Accepted accepted => accepted.Policy,
            RegistryLoadOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
}
