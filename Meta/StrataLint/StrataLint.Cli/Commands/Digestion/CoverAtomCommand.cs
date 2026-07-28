using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

// Phase 1 cover transaction: bind one already-proven Lean declaration to an
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
// digestion-formalization-v1 receipt supplied by --envelope. The receipt binds
// atom_id + primary_gid + the atom's content fingerprint (cas_ref/raw_sha256), and
// the deposited declaration's current signature (name_key/kind/type) must equal the
// signature the formalizer pinned before the proof landed. This replaces the old
// file-level newness heuristic: it is base-agnostic (survives the two-phase deposit
// where the declaration is base-owned) yet rejects a post-proof statement swap and
// prevents an arbitrary --base from laundering an old declaration as new.
//
// Deferred (recorded, not silent):
//  - Hollow-fidelity attestation (§4b): signature-match proves deposited ==
//    pre-committed, but not that the pre-committed signature is itself a faithful,
//    non-hollow rendering of the natural-language atom. A hollow pre-commit
//    (`theorem t : True`) deposited unchanged would pass. That needs the separate
//    digestion-fidelity-attestation-v1 receipt + /sshx multi-model consensus.
//  - Receipt emission + residence: the formalizer/workflow (step 1) is responsible
//    for producing and committing the receipt at a digestion data path; this
//    command only consumes it. Receipt lifecycle (deletion after absorption) is a
//    workflow concern.
//  - kind exclusion gate (spec §5): a producer responsibility, not cover's.
internal static class CoverAtomCommand
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
            var document = LoadDocument(current, "candidate");
            var baselineDocument = LoadDocument(baseline, "baseline");

            // Gate ②(a): the cover GID must select a Lean declaration, not just a
            // module (module-level coverage is ingest's residual boundary, not a
            // single truth atom).
            if (!Gid.TryParse(options.Gid, out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: not null })
            {
                throw new InvalidOperationException(
                    $"cover GID must select a Lean declaration: {options.Gid}");
            }

            // Gate ①: locate the single open, still-uncovered target atom.
            var sources = document.RequireDigestionSources();
            var target = LocateTarget(sources, options.AtomId);

            // Gate ②(b): anti-Goodhart — cover may only deposit a declaration that
            // the baseline ledger did not already bind.
            if (BaselineCoverageGids(baselineDocument).Contains(options.Gid))
            {
                throw new InvalidOperationException(
                    $"cover GID {options.Gid} is already bound in the baseline ledger");
            }

            // Gate ②(c) is now a declaration-signature match against the
            // pre-committed formalization receipt (spec §4a); it runs after the
            // Closed-deletable gate below so that a genuinely missing/ambiguous
            // declaration reports through the standard gap path first. See the
            // `DigestionFormalizationReceipt.Load` + RequireEnvelopeBinding +
            // RequireSignatureMatch block near the end of the transaction.

            // Gate ⑤: the declaration may not already be bound to any other atom in
            // the candidate ledger (unique GID -> atom mapping).
            if (FindCrossAtomBinding(sources, options.AtomId, options.Gid) is { } conflict)
            {
                throw new InvalidOperationException(
                    $"cover GID {options.Gid} is already bound to atom {conflict}");
            }

            var receipts = BuildReceipts(target, gid, current);
            var covered = target with
            {
                CoverageGids = ImmutableArray.Create(options.Gid),
                Receipts = target.Receipts with
                {
                    Coverage = ImmutableArray.Create(receipts.Coverage),
                    Scribe = ImmutableArray.Create(receipts.Scribe),
                },
                ReceiptSyntax = null,
            };
            var plannedDocument = ReplaceEntry(document, options.AtomId, covered);

            var report = leanReportSource.Load(current);
            var lean = ValidateLean(current, report);
            var verifiedScribeEmissions = scribeEmissionVerifier.Verify(report);

            var derived = DigestionStatusEvaluator.Evaluate(
                plannedDocument,
                current,
                lean,
                verifiedScribeEmissions,
                baselineDocument,
                validateProjectedStatus: false);
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

            var finalBytes = BackfillInventoryWriter.WriteForIngest(refreshed);
            var finalRaw = ReplaceLedger(currentRaw, finalBytes);
            var finalSnapshot = Decode(finalRaw);
            var finalDocument = LoadDocument(finalSnapshot, "final");
            var evaluation = DigestionStatusEvaluator.Evaluate(
                finalDocument,
                finalSnapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument);
            RequireNoFindings(evaluation);
            RequireValidBackfill(
                finalDocument,
                finalSnapshot,
                baseline,
                LoadPolicy(finalSnapshot),
                lean,
                verifiedScribeEmissions);

            // Gate ③/④/⑥: the covered atom must reach a deletable *Closed* state
            // with zero gaps — spec §3.4 ③ requires TruthDag=Closed and no
            // sorry/private/unregistered axiom, so an absorbed-tail (any
            // non-standard axiom present) is rejected, not written. Anything short
            // of Closed — a missing/sorry-only declaration, an unverified Scribe
            // emission, a drifted receipt — is refused.
            RequireClosedDeletable(EvaluationFor(evaluation, options.AtomId));

            // Gate ②(c): pre-committed formalization receipt + declaration-signature
            // match (spec §4a). Replaces the old file-level newness gate. The
            // formalizer pins the atom's primary declaration signature
            // (name_key/kind/type) before the proof lands; cover admits the
            // declaration only when its *current* signature in the raw Lean report
            // equals the pinned signature. This is base-agnostic — the honest
            // two-phase deposit (freeze in PR-1, cover in PR-2 with --base
            // origin/dev) is accepted because no file-byte comparison is made —
            // while a post-proof statement swap (e.g. to `True`) is rejected because
            // the deposited signature then diverges. The receipt also binds atom_id
            // + primary_gid + the atom's content fingerprint, so a receipt pinned for
            // one atom cannot cover another (anti-Goodhart); an arbitrary --base is
            // therefore no longer able to launder an old declaration as new.
            //
            // Deferred (§4b, recorded not silent): this does not attest that the
            // pre-committed signature is itself a faithful, non-hollow rendering of
            // the natural-language atom — a hollow pre-commit deposited unchanged
            // would pass. That is the separate digestion-fidelity-attestation-v1 /
            // multi-model consensus gate, out of scope for this block.
            var receipt = DigestionFormalizationReceipt.Load(current, options.EnvelopePath);
            RequireEnvelopeBinding(receipt, options, target);
            RequireSignatureMatch(receipt, gid, report);

            var currentLedger = currentRaw.Entries.Single(static entry =>
                entry.Path == BackfillInventoryLoader.RelativePath);
            var changed = !currentLedger.Bytes.AsSpan().SequenceEqual(finalBytes.AsSpan());
            if (changed)
            {
                var outputPath = Path.Combine(
                    Path.GetFullPath(repositoryRoot),
                    BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar));

                // Check-then-act guard (fail-closed): re-read the ledger from disk
                // and confirm it still exists and matches the bytes we validated
                // against. Two concurrent covers can both validate against the same
                // ledger L; without this the second write would clobber the first
                // deposit (lost update). A missing file is treated as drift and
                // aborts too — never re-create a ledger that disappeared under us.
                // NOTE: this is not a true CAS/lock; a sub-millisecond residual
                // TOCTOU window remains between this reread and the atomic rename.
                // Serialized manual/CI invocation makes that sufficient; a hard
                // guarantee needs an OS file lock (deferred).
                if (!File.Exists(outputPath))
                {
                    throw new InvalidOperationException(
                        "ledger went missing between read and write; "
                        + "aborting to avoid a lost update");
                }

                if (!File.ReadAllBytes(outputPath).AsSpan()
                        .SequenceEqual(currentLedger.Bytes.AsSpan()))
                {
                    throw new InvalidOperationException(
                        "ledger changed under us between read and write; "
                        + "aborting to avoid a lost update");
                }

                IngestCommand.ReplaceLedgerAtomically(outputPath, finalBytes.AsSpan());
            }

            return new CommandResult(
                true,
                $"COVER atom_id={options.AtomId} gid={options.Gid} "
                + $"ledger_changed={changed.ToString().ToLowerInvariant()}\n"
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
        string atomId)
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
        if (entry.CoverageGids.Length > 0)
        {
            throw new InvalidOperationException(
                $"cover atom {atomId} already has coverage: "
                + string.Join(", ", entry.CoverageGids));
        }

        if (entry.ProjectedStatus.Truth != DigestionTruthState.Open)
        {
            throw new InvalidOperationException(
                $"cover atom {atomId} is not open "
                + $"(truth={DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)})");
        }

        return entry;
    }

    private static ImmutableHashSet<string> BaselineCoverageGids(
        BackfillInventoryDocument baselineDocument) =>
        baselineDocument.RequireDigestionEntries()
            .SelectMany(static entry => entry.CoverageGids)
            .ToImmutableHashSet(StringComparer.Ordinal);

    private static string? FindCrossAtomBinding(
        ImmutableArray<DigestionLedgerSource> sources,
        string atomId,
        string gid) =>
        sources
            .SelectMany(static source => source.Entries)
            .Where(entry => !string.Equals(entry.AtomId, atomId, StringComparison.Ordinal))
            .Where(entry => entry.CoverageGids.Contains(gid, StringComparer.Ordinal))
            .Select(static entry => entry.AtomId)
            .FirstOrDefault();

    private static (DigestionCoverageReceipt Coverage, DigestionScribeReceipt Scribe) BuildReceipts(
        DigestionLedgerEntry entry,
        Gid gid,
        RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile(gid.Path.Value, out var target))
        {
            throw new InvalidOperationException($"cover target Lean file is absent: {gid.Path.Value}");
        }

        var documentGid = ScribeEmissionAttestation.DocumentGid(gid.Value);
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(documentGid);
        if (!snapshot.TryGetFile(definitionPath, out var definition))
        {
            throw new InvalidOperationException($"cover Scribe definition is absent: {definitionPath}");
        }

        if (!snapshot.TryGetFile(emissionPath, out var emission))
        {
            throw new InvalidOperationException($"cover Scribe emission is absent: {emissionPath}");
        }

        var coverage = new DigestionCoverageReceipt(
            gid.Value,
            entry.Fingerprints.RawSha256,
            DigestionFingerprint.Compute(target.RawBytes.AsSpan()).RawSha256);
        var scribe = new DigestionScribeReceipt(
            gid.Value,
            DigestionFingerprint.Compute(definition.RawBytes.AsSpan()).RawSha256,
            DigestionFingerprint.Compute(emission.RawBytes.AsSpan()).RawSha256);
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

        if (!string.Equals(receipt.PrimaryGid, options.Gid, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"cover envelope primary_gid {receipt.PrimaryGid} does not match --gid {options.Gid}");
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
        LeanAxiomReport report)
    {
        var deposited = DepositedSignature(gid, report);
        if (deposited != receipt.Signature)
        {
            throw new InvalidOperationException(
                $"cover declaration {gid.Value} signature "
                + $"({deposited.NameKey}, {deposited.Kind}, {deposited.Type}) "
                + "does not match the pre-committed signature "
                + $"({receipt.Signature.NameKey}, {receipt.Signature.Kind}, {receipt.Signature.Type})");
        }
    }

    // Resolve the deposited declaration's canonical signature from the raw Lean
    // report, using the same GID-selector matching as DigestionStatusEvaluator.
    // By the time this runs the Closed-deletable gate has already established the
    // declaration exists and is unique, so a zero/multiple match here is a
    // fail-closed invariant breach rather than the normal missing-declaration path.
    private static DigestionFormalizationSignature DepositedSignature(Gid gid, LeanAxiomReport report)
    {
        if (gid.ToTarget() is not Target.Formal { Declaration: { } selector } formal)
        {
            throw new InvalidOperationException($"cover GID must select a Lean declaration: {gid.Value}");
        }

        if (!report.Files.TryGetValue(formal.Path, out var module) || !string.IsNullOrEmpty(module.Error))
        {
            throw new InvalidOperationException(
                $"cover declaration is absent from the Lean report: {gid.Value}");
        }

        var suffix = "." + selector;
        var matches = module.Declarations
            .Where(candidate => string.Equals(candidate.Name, selector, StringComparison.Ordinal)
                || candidate.Name.EndsWith(suffix, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length != 1)
        {
            throw new InvalidOperationException(
                $"cover declaration {gid.Value} resolves to {matches.Length} report declarations");
        }

        var declaration = matches[0];
        return new DigestionFormalizationSignature(
            declaration.NameKey,
            declaration.Kind,
            declaration.TypeRepresentation);
    }

    private sealed record CoverArguments(string AtomId, string Gid, string BaselineRevision, string EnvelopePath);

    private static CoverArguments ParseArguments(IReadOnlyList<string> arguments)
    {
        string? atomId = null;
        string? gid = null;
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
                case "--gid" when gid is null:
                    gid = arguments[index + 1];
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
            || string.IsNullOrWhiteSpace(gid)
            || string.IsNullOrWhiteSpace(baselineRevision)
            || string.IsNullOrWhiteSpace(envelopePath))
        {
            throw Usage();
        }

        return new CoverArguments(atomId, gid, baselineRevision, envelopePath);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint cover-atom --cover-atom ATOM_ID --gid DECL_GID --base REV "
        + "--envelope RECEIPT_PATH");

    private static BackfillInventoryDocument LoadDocument(RepositorySnapshot snapshot, string side)
    {
        if (!snapshot.TryGetFile(BackfillInventoryLoader.RelativePath, out var file))
        {
            throw new InvalidOperationException(
                $"{side} {BackfillInventoryLoader.RelativePath} is missing");
        }

        return BackfillInventoryLoader.Load(file.Text);
    }

    private static RawRepositorySnapshot ReplaceLedger(
        RawRepositorySnapshot snapshot,
        ImmutableArray<byte> bytes)
    {
        var matches = snapshot.Entries.Count(static entry =>
            entry.Path == BackfillInventoryLoader.RelativePath);
        if (matches != 1)
        {
            throw new InvalidOperationException(
                $"snapshot must contain exactly one {BackfillInventoryLoader.RelativePath}");
        }

        return RawRepositorySnapshot.Create(snapshot.Entries.Select(entry =>
            entry.Path == BackfillInventoryLoader.RelativePath
                ? new RawRepositoryEntry(entry.Path, bytes)
                : entry));
    }

    private static void RequireNoFindings(DigestionLedgerEvaluation evaluation)
    {
        if (evaluation.Findings.Length > 0)
        {
            throw new InvalidOperationException(
                "digest status is invalid: " + string.Join("; ", evaluation.Findings));
        }
    }

    private static void RequireValidBackfill(
        BackfillInventoryDocument document,
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        VerifiedScribeEmissions verifiedScribeEmissions)
    {
        var findings = BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(
                current,
                baseline,
                policy,
                lean,
                verifiedScribeEmissions),
            document);
        if (findings.Length > 0)
        {
            throw new InvalidOperationException(
                "SL-016 final ledger is invalid: "
                + string.Join("; ", findings.Select(static finding => finding.Message)));
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
