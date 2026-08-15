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
        var current = Decode(currentRaw);
        var document = LoadDocument(current);
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
        var verified = scribeEmissionVerifier.Verify(report);
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
            ReceiptSyntax = null,
        };
        var planned = ReplaceEntry(document, options.AtomId, alignedEntry);
        var derived = DigestionStatusEvaluator.Evaluate(
            planned,
            current,
            lean,
            verified,
            baselineDocument: null,
            validateProjectedStatus: false);
        RequireNoConflictMarkedSources(derived);
        RequireAlignedScribeReceipt(EvaluationFor(derived, options.AtomId), options.Gid);
        var finalBytes = BackfillInventoryWriter.WriteForIngest(planned);
        var finalRaw = IngestCommand.ReplaceLedger(
            currentRaw,
            document,
            planned,
            finalBytes);
        var finalSnapshot = Decode(finalRaw);
        var finalDocument = LoadDocument(finalSnapshot);
        var finalEvaluation = DigestionStatusEvaluator.Evaluate(
            finalDocument,
            finalSnapshot,
            lean,
            verified,
            baselineDocument: null);
        RequireNoConflictMarkedSources(finalEvaluation);
        RequireAlignedScribeReceipt(EvaluationFor(finalEvaluation, options.AtomId), options.Gid);

        var ledgerUpdates = IngestCommand.LedgerUpdates(currentRaw, finalRaw);
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
        if (arguments.Count != 4)
        {
            throw AlignUsage();
        }

        string? atomId = null;
        string? gid = null;
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
                default:
                    throw AlignUsage();
            }
        }

        if (string.IsNullOrWhiteSpace(atomId) || string.IsNullOrWhiteSpace(gid))
        {
            throw AlignUsage();
        }

        return new AlignArguments(atomId, gid);
    }

    private static InvalidOperationException AlignUsage() => new(
        "USAGE: StrataLint align-scribe-receipt --atom-id ATOM_ID --gid GID");

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
