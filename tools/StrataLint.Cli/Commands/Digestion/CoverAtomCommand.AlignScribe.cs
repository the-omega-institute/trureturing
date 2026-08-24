using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

// align-scribe 动词:只修复目标条目的 Scribe 收据(cover 的姊妹路径),与其专属参数解析
// 及守卫同居;主文件保留 cover 事务与共享辅助。
internal static partial class CoverAtomCommand
{
    internal static CommandResult AlignScribeReceipt(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        var options = ParseAlignArguments(arguments);
        var currentRaw = repository.ReadCurrent();
        var baselineRaw = repository.ReadRevision(options.BaselineRevision);
        var current = Decode(currentRaw);
        var baseline = Decode(baselineRaw);
        var document = LoadDocument(current);
        var baselineDocument = BackfillInventoryLoader.LoadBaseline(baseline);
        var matches = document.RequireDigestionEntries()
            .Where(entry => string.Equals(entry.AtomId, options.AtomId, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length != 1)
        {
            throw new InvalidOperationException(
                matches.Length == 0
                    ? $"align atom {options.AtomId} is absent from the ledger"
                    : $"align atom {options.AtomId} is ambiguous in the ledger");
        }

        var target = matches[0];
        if (target.CoverageGids.Count(gid =>
                string.Equals(gid, options.Gid, StringComparison.Ordinal)) != 1)
        {
            throw new InvalidOperationException(
                $"align GID {options.Gid} must occur exactly once in atom {options.AtomId} coverage_gids");
        }

        var receiptMatches = target.Receipts.Scribe
            .Where(receipt => string.Equals(receipt.Gid, options.Gid, StringComparison.Ordinal))
            .ToArray();
        if (receiptMatches.Length != 1)
        {
            throw new InvalidOperationException(
                $"align GID {options.Gid} must have exactly one Scribe receipt in atom {options.AtomId}");
        }

        if (!Gid.TryParse(options.Gid, out var gid)
            || gid.ToTarget() is not Target.Formal { Declaration: not null })
        {
            throw new InvalidOperationException(
                $"align GID must select a Lean declaration: {options.Gid}");
        }

        var report = leanReportSource.Load(current);
        var lean = ValidateLean(current, report);
        var verified = scribeEmissionVerifier.Verify(current, report);
        var changes = repository.ReadChanges(options.BaselineRevision);
        var forkDeltaEvaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            current,
            lean,
            verified,
            baselineDocument,
            baselineSnapshot: baseline,
            changes: changes);
        var forkPointDocument = DigestionReceiptIntegrity.ForkPointView(
            document,
            baselineDocument);
        var forkPointEvaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            forkPointDocument,
            baseline,
            lean,
            verified,
            forkPointDocument,
            baselineSnapshot: baseline,
            changes: changes);
        var exactRepairIdentities = DigestionReceiptIntegrity.ExactScribeRepairIdentities(
            forkDeltaEvaluation,
            options.AtomId,
            options.Gid);
        DigestionReceiptIntegrityGuard.RequireNoNewFailures(
            forkPointEvaluation,
            forkDeltaEvaluation,
            exactRepairIdentities);
        var documentGid = ScribeEmissionAttestation.DocumentGid(options.Gid);
        if (!verified.TryGet(documentGid, out var verifiedRecord)
            || !verified.ReferencesDeclaration(options.Gid))
        {
            throw new InvalidOperationException(
                $"align GID {options.Gid} has no verified Scribe emission and declaration reference");
        }

        var oldReceipt = receiptMatches[0];
        var newReceipt = oldReceipt with
        {
            DefinitionSha256 = verifiedRecord.DefinitionSha256,
            EmissionSha256 = verifiedRecord.EmissionSha256,
        };
        var alignedEntry = target with
        {
            Receipts = target.Receipts with
            {
                Scribe = target.Receipts.Scribe
                    .Select(receipt => string.Equals(receipt.Gid, options.Gid, StringComparison.Ordinal)
                            ? newReceipt
                            : receipt)
                    .ToImmutableArray(),
            },
        };
        var planned = ReplaceEntry(document, options.AtomId, alignedEntry);
        var derived = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            planned,
            current,
            lean,
            verified,
            baselineDocument: null,
            validateProjectedStatus: false);
        RequireNoConflictMarkedSources(derived);
        DigestionReceiptIntegrityGuard.RequireExactScribeRepairComplete(
            derived,
            options.AtomId,
            options.Gid);
        var finalRaw = IngestCommand.ReplaceLedger(
            currentRaw,
            document,
            planned);
        var finalSnapshot = Decode(finalRaw);
        var finalDocument = LoadDocument(finalSnapshot);
        var ledgerUpdates = IngestCommand.LedgerUpdates(currentRaw, finalRaw);
        var plannedChanges = DigestionReceiptIntegrityGuard.IncludePlannedPaths(
            changes,
            ledgerUpdates.Select(static update => update.Path));
        var beforePlannedEvaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            current,
            lean,
            verified,
            baselineDocument,
            baselineSnapshot: baseline,
            changes: plannedChanges);
        var plannedEvaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            finalDocument,
            finalSnapshot,
            lean,
            verified,
            baselineDocument,
            baselineSnapshot: baseline,
            changes: plannedChanges);
        DigestionReceiptIntegrityGuard.RequireNoNewFailures(
            beforePlannedEvaluation,
            plannedEvaluation);
        var finalEvaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            finalDocument,
            finalSnapshot,
            lean,
            verified,
            baselineDocument: null);
        RequireNoConflictMarkedSources(finalEvaluation);
        DigestionReceiptIntegrityGuard.RequireExactScribeRepairComplete(
            finalEvaluation,
            options.AtomId,
            options.Gid);

        var changed = ledgerUpdates.Length > 0;
        IngestCommand.ApplyLedgerUpdatesAtomically(repositoryRoot, currentRaw, ledgerUpdates);

        return new CommandResult(
            true,
            $"ALIGN_SCRIBE_RECEIPT atom_id={options.AtomId} gid={options.Gid} "
            + $"old_definition_sha256={oldReceipt.DefinitionSha256} "
            + $"new_definition_sha256={newReceipt.DefinitionSha256} "
            + $"old_emission_sha256={oldReceipt.EmissionSha256} "
            + $"new_emission_sha256={newReceipt.EmissionSha256} "
            + $"ledger_changed={changed.ToString().ToLowerInvariant()}\n",
            string.Empty);
    }

    private static AlignArguments ParseAlignArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 6)
        {
            throw AlignUsage();
        }

        string? atomId = null;
        string? gid = null;
        string? baselineRevision = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count)
            {
                throw AlignUsage();
            }

            switch (arguments[index])
            {
                case "--atom-id" when atomId is null:
                    atomId = arguments[index + 1];
                    break;
                case "--gid" when gid is null:
                    gid = arguments[index + 1];
                    break;
                case "--base" when baselineRevision is null:
                    baselineRevision = arguments[index + 1];
                    break;
                default:
                    throw AlignUsage();
            }
        }

        if (string.IsNullOrWhiteSpace(atomId)
            || string.IsNullOrWhiteSpace(gid)
            || string.IsNullOrWhiteSpace(baselineRevision))
        {
            throw AlignUsage();
        }

        return new AlignArguments(atomId, gid, baselineRevision);
    }

    private static InvalidOperationException AlignUsage() => new(
        "USAGE: StrataLint align-scribe-receipt --atom-id ATOM_ID --gid GID --base REV");

    // align-scribe 刻意容忍同胞条目的状态漂移与 coverage 诊断(既有契约,见 CoverAtomTests
    // AlignScribeReceiptIgnoresSiblingDrift…);唯独源文本含冲突标记时不得写账本。
    private static void RequireNoConflictMarkedSources(DigestionLedgerEvaluation evaluation)
    {
        var conflicts = evaluation.Findings
            .Where(static finding => finding.Contains(
                DigestionSourceConflictMarkers.DiagnosticCode,
                StringComparison.Ordinal))
            .ToArray();
        if (conflicts.Length > 0)
        {
            throw new InvalidOperationException(
                "digest status is invalid: " + string.Join("; ", conflicts));
        }
    }
}
