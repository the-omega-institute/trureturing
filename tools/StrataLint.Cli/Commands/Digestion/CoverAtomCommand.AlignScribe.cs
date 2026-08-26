using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

// align-scribe 动词:只修复目标条目的 Scribe 收据(cover 的姊妹路径),与其专属参数解析
// 及守卫同居;主文件保留 cover 事务与共享辅助。
// 接受一对或多对 (--atom-id, --gid):终评是全库校验,存量 mismatch 互为否决,故修复
// 必须能在一个事务里对齐全部受影响收据、只验一次(#3297 判例:逐对顺序修不可收敛)。
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
        var report = leanReportSource.Load(current);
        var lean = ValidateLean(current, report);
        var truthStates = LeanTruthStates.Resolve(current, lean);
        var verified = scribeEmissionVerifier.Verify(current, report);

        var planned = document;
        var outputLines = new List<string>();
        foreach (var pair in options.Pairs)
        {
            var matches = planned.RequireDigestionEntries()
                .Where(entry => string.Equals(entry.AtomId, pair.AtomId, StringComparison.Ordinal))
                .ToArray();
            if (matches.Length != 1)
            {
                throw new InvalidOperationException(
                    matches.Length == 0
                        ? $"align atom {pair.AtomId} is absent from the ledger"
                        : $"align atom {pair.AtomId} is ambiguous in the ledger");
            }

            var target = matches[0];
            if (target.CoverageGids.Count(gid =>
                    string.Equals(gid, pair.Gid, StringComparison.Ordinal)) != 1)
            {
                throw new InvalidOperationException(
                    $"align GID {pair.Gid} must occur exactly once in atom {pair.AtomId} coverage_gids");
            }

            var receiptMatches = target.Receipts.Scribe
                .Where(receipt => string.Equals(receipt.Gid, pair.Gid, StringComparison.Ordinal))
                .ToArray();
            if (receiptMatches.Length != 1)
            {
                throw new InvalidOperationException(
                    $"align GID {pair.Gid} must have exactly one Scribe receipt in atom {pair.AtomId}");
            }

            if (!Gid.TryParse(pair.Gid, out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: not null })
            {
                throw new InvalidOperationException(
                    $"align GID must select a Lean declaration: {pair.Gid}");
            }

            var documentGid = ScribeEmissionAttestation.DocumentGid(pair.Gid);
            if (!verified.TryGet(documentGid, out var verifiedRecord)
                || !verified.ReferencesDeclaration(pair.Gid))
            {
                throw new InvalidOperationException(
                    $"align GID {pair.Gid} has no verified Scribe emission and declaration reference");
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
                        .Select(receipt => string.Equals(receipt.Gid, pair.Gid, StringComparison.Ordinal)
                                ? newReceipt
                                : receipt)
                        .ToImmutableArray(),
                },
            };
            planned = ReplaceEntry(planned, pair.AtomId, alignedEntry);
            outputLines.Add(
                $"ALIGN_SCRIBE_RECEIPT atom_id={pair.AtomId} gid={pair.Gid} "
                + $"old_definition_sha256={oldReceipt.DefinitionSha256} "
                + $"new_definition_sha256={newReceipt.DefinitionSha256} "
                + $"old_emission_sha256={oldReceipt.EmissionSha256} "
                + $"new_emission_sha256={newReceipt.EmissionSha256} ");
        }

        var derived = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            planned,
            current,
            lean,
            verified,
            baselineDocument,
            validateProjectedStatus: false,
            baselineSnapshot: baseline,
            truthStates: truthStates);
        RequireNoConflictMarkedSources(derived);
        foreach (var pair in options.Pairs)
        {
            RequireAlignedScribeReceipt(EvaluationFor(derived, pair.AtomId), pair.Gid);
        }

        var finalRaw = IngestCommand.ReplaceLedger(
            currentRaw,
            document,
            planned);
        var finalSnapshot = Decode(finalRaw);
        LeanTruthStates.RequireSameManagedInputs(current, finalSnapshot);
        var finalDocument = LoadDocument(finalSnapshot);
        var finalEvaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            finalDocument,
            finalSnapshot,
            lean,
            verified,
            baselineDocument,
            baselineSnapshot: baseline,
            truthStates: truthStates);
        RequireNoConflictMarkedSources(finalEvaluation);
        foreach (var pair in options.Pairs)
        {
            RequireAlignedScribeReceipt(EvaluationFor(finalEvaluation, pair.AtomId), pair.Gid);
        }

        IngestCommand.RequireNoReceiptIntegrityFailure(finalEvaluation);

        var ledgerUpdates = IngestCommand.LedgerUpdates(currentRaw, finalRaw);
        var changed = ledgerUpdates.Length > 0;
        IngestCommand.ApplyLedgerUpdatesAtomically(repositoryRoot, currentRaw, ledgerUpdates);

        var suffix = $"ledger_changed={changed.ToString().ToLowerInvariant()}\n";
        return new CommandResult(
            true,
            string.Concat(outputLines.Select(line => line + suffix)),
            string.Empty);
    }

    private static void RequireAlignedScribeReceipt(DigestionEntryEvaluation target, string gid)
    {
        var targetGaps = target.Gaps
            .Where(gap => string.Equals(gap.Detail, gid, StringComparison.Ordinal))
            .Where(static gap => gap.Code is
                "scribe-definition-mismatch" or "scribe-emission-mismatch")
            .ToArray();
        if (targetGaps.Length == 0)
        {
            return;
        }

        throw new InvalidOperationException(
            $"align target {target.Entry.AtomId} remains invalid for {gid}: "
            + string.Join(",", targetGaps.Select(static gap => gap.Code)));
    }

    private static AlignArguments ParseAlignArguments(IReadOnlyList<string> arguments)
    {
        string? baselineRevision = null;
        string? pendingAtomId = null;
        var pairs = ImmutableArray.CreateBuilder<AlignPair>();
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count)
            {
                throw AlignUsage();
            }

            var value = arguments[index + 1];
            switch (arguments[index])
            {
                case "--atom-id" when pendingAtomId is null:
                    pendingAtomId = value;
                    break;
                case "--gid" when pendingAtomId is not null:
                    pairs.Add(new AlignPair(pendingAtomId, value));
                    pendingAtomId = null;
                    break;
                case "--base" when baselineRevision is null:
                    baselineRevision = value;
                    break;
                default:
                    throw AlignUsage();
            }
        }

        if (pendingAtomId is not null
            || pairs.Count == 0
            || string.IsNullOrWhiteSpace(baselineRevision)
            || pairs.Any(pair =>
                string.IsNullOrWhiteSpace(pair.AtomId) || string.IsNullOrWhiteSpace(pair.Gid))
            || pairs.Distinct().Count() != pairs.Count)
        {
            throw AlignUsage();
        }

        return new AlignArguments(pairs.ToImmutable(), baselineRevision);
    }

    private static InvalidOperationException AlignUsage() => new(
        "USAGE: StrataLint align-scribe-receipt (--atom-id ATOM_ID --gid GID)+ --base REV");

    // align-scribe 只容忍非致命 gap;源文本冲突与其余 receipt-integrity failure
    // 均不得写账本。
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
