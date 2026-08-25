using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    internal static CommandResult RealignReceipts(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        try
        {
            var baselineRevision = ParseRealignArguments(arguments);
            var currentRaw = repository.ReadCurrent();
            var baselineRaw = repository.ReadRevision(baselineRevision);
            var current = Decode(currentRaw);
            var baseline = Decode(baselineRaw);
            var document = LoadDocument(current);
            var baselineDocument = BackfillInventoryLoader.LoadBaseline(baseline);
            RequireUnchangedCoverageClaims(document, baselineDocument);
            var report = leanReportSource.Load(current);
            var lean = ValidateLean(current, report);
            var verified = scribeEmissionVerifier.Verify(current, report);
            var beforeEvaluation = DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.FullScan,
                document,
                current,
                lean,
                verified,
                baselineDocument,
                baselineSnapshot: baseline);
            var fatalGapsBefore = beforeEvaluation.ReceiptIntegrityGaps.Count();
            var counts = new ReceiptRealignmentCounts();
            var aligned = document.WithDigestionSources(
                document.RequireDigestionSources()
                    .Select(source => source with
                    {
                        Entries = source.Entries
                            .Select(entry => RealignEntry(entry, current, verified, counts))
                            .ToImmutableArray(),
                    })
                    .ToImmutableArray());
            var derived = DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.FullScan,
                aligned,
                current,
                lean,
                verified,
                baselineDocument,
                validateProjectedStatus: false,
                baselineSnapshot: baseline);
            RequireNoReceiptIntegrityFailure(derived);
            RequireUnchangedAbsorbedDeclarationSignatures(
                derived,
                baseline,
                report);
            var statusByAtomId = derived.Entries.ToDictionary(
                static item => item.Entry.AtomId,
                static item => item.DerivedStatus,
                StringComparer.Ordinal);
            var refreshed = aligned.WithDigestionSources(
                aligned.RequireDigestionSources()
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
            var finalRaw = ReplaceLedger(currentRaw, document, refreshed);
            var finalSnapshot = Decode(finalRaw);
            var finalDocument = LoadDocument(finalSnapshot);
            RequireFinalReceiptRealignmentFullScan(
                finalDocument,
                finalSnapshot,
                lean,
                verified,
                baselineDocument,
                baseline);
            var ledgerUpdates = LedgerUpdates(currentRaw, finalRaw);
            ApplyLedgerUpdatesAtomically(repositoryRoot, currentRaw, ledgerUpdates);

            return new CommandResult(
                true,
                $"REALIGN_RECEIPTS fatal_gaps_repaired={fatalGapsBefore} "
                + $"coverage_receipts_changed={counts.CoverageReceiptsChanged} "
                + $"scribe_receipts_changed={counts.ScribeReceiptsChanged} "
                + $"entries_changed={counts.EntriesChanged} "
                + $"files_changed={ledgerUpdates.Length} "
                + $"ledger_changed={(ledgerUpdates.Length > 0).ToString().ToLowerInvariant()}\n"
                + $"ledger_sha256_before={DigestionLedgerPreimage.ComputeSha256(document)}\n"
                + $"ledger_sha256_after={DigestionLedgerPreimage.ComputeSha256(finalDocument)}\n",
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"REALIGN_RECEIPTS_INVALID {exception.Message}\n");
        }
    }

    private static DigestionLedgerEntry RealignEntry(
        DigestionLedgerEntry entry,
        RepositorySnapshot snapshot,
        VerifiedScribeEmissions verified,
        ReceiptRealignmentCounts counts)
    {
        RequireExactOneReceipts(
            entry,
            entry.Receipts.Coverage.Select(static receipt => receipt.Gid),
            "coverage");
        RequireExactOneReceipts(
            entry,
            entry.Receipts.Scribe.Select(static receipt => receipt.Gid),
            "Scribe");

        var coverageChanged = 0;
        var coverage = entry.Receipts.Coverage.Select(receipt =>
        {
            if (entry.CoverageGids.Count(gid => string.Equals(
                    gid,
                    receipt.Gid,
                    StringComparison.Ordinal)) != 1)
            {
                throw new InvalidOperationException(
                    $"atom {entry.AtomId} receipt GID {receipt.Gid} must occur exactly once in coverage_gids");
            }
            if (!Gid.TryParse(receipt.Gid, out var gid)
                || !snapshot.TryGetFile(gid.Path.Value, out var target))
            {
                throw new InvalidOperationException(
                    $"atom {entry.AtomId} coverage target is unavailable: {receipt.Gid}");
            }

            var replacement = receipt with
            {
                SourceSha256 = entry.Fingerprints.RawSha256,
                TargetSha256 = DigestionFingerprint.Compute(target.RawBytes.AsSpan()).RawSha256,
            };
            if (replacement != receipt) coverageChanged++;
            return replacement;
        }).ToImmutableArray();

        var scribeChanged = 0;
        var scribe = entry.Receipts.Scribe.Select(receipt =>
        {
            if (entry.CoverageGids.Count(gid => string.Equals(
                    gid,
                    receipt.Gid,
                    StringComparison.Ordinal)) != 1)
            {
                throw new InvalidOperationException(
                    $"atom {entry.AtomId} receipt GID {receipt.Gid} must occur exactly once in coverage_gids");
            }

            var documentGid = ScribeEmissionAttestation.DocumentGid(receipt.Gid);
            if (!verified.TryGet(documentGid, out var record))
            {
                throw new InvalidOperationException(
                    $"atom {entry.AtomId} has no verified Scribe emission for {receipt.Gid}");
            }
            if (Gid.TryParse(receipt.Gid, out var gid)
                && gid.ToTarget() is Target.Formal { Declaration: not null }
                && !verified.ReferencesDeclaration(receipt.Gid))
            {
                throw new InvalidOperationException(
                    $"atom {entry.AtomId} has no verified Scribe declaration reference for {receipt.Gid}");
            }

            var replacement = receipt with
            {
                DefinitionSha256 = record.DefinitionSha256,
                EmissionSha256 = record.EmissionSha256,
            };
            if (replacement != receipt) scribeChanged++;
            return replacement;
        }).ToImmutableArray();

        counts.CoverageReceiptsChanged += coverageChanged;
        counts.ScribeReceiptsChanged += scribeChanged;
        if (coverageChanged + scribeChanged > 0) counts.EntriesChanged++;
        return entry with
        {
            Receipts = entry.Receipts with
            {
                Coverage = coverage,
                Scribe = scribe,
            },
        };
    }

    private static void RequireExactOneReceipts(
        DigestionLedgerEntry entry,
        IEnumerable<string> receiptGids,
        string kind)
    {
        var duplicate = receiptGids
            .GroupBy(static gid => gid, StringComparer.Ordinal)
            .FirstOrDefault(static group => group.Count() != 1);
        if (duplicate is not null)
        {
            throw new InvalidOperationException(
                $"atom {entry.AtomId} GID {duplicate.Key} must have exactly one {kind} receipt");
        }
    }

    private static void RequireUnchangedCoverageClaims(
        BackfillInventoryDocument current,
        BackfillInventoryDocument baseline)
    {
        var currentByAtom = current.RequireDigestionEntries().ToDictionary(
            static entry => entry.AtomId,
            StringComparer.Ordinal);
        var baselineByAtom = baseline.RequireDigestionEntries().ToDictionary(
            static entry => entry.AtomId,
            StringComparer.Ordinal);
        foreach (var atomId in currentByAtom.Keys.Union(baselineByAtom.Keys, StringComparer.Ordinal))
        {
            var currentCoverage = currentByAtom.TryGetValue(atomId, out var currentEntry)
                ? currentEntry.CoverageGids
                : [];
            var baselineCoverage = baselineByAtom.TryGetValue(atomId, out var baselineEntry)
                ? baselineEntry.CoverageGids
                : [];
            if (!currentCoverage.ToHashSet(StringComparer.Ordinal)
                    .SetEquals(baselineCoverage))
            {
                throw new InvalidOperationException(
                    $"atom {atomId} coverage claim changed relative to the baseline");
            }
        }
    }

    private static void RequireUnchangedAbsorbedDeclarationSignatures(
        DigestionLedgerEvaluation evaluation,
        RepositorySnapshot baseline,
        LeanAxiomReport currentReport)
    {
        foreach (var item in evaluation.Entries.Where(static item =>
                     item.DerivedStatus.Migration == DigestionMigrationState.Absorbed))
        {
            var entry = item.Entry;
            var receiptPath = DigestionFormalizationReceipt.PathForAtom(entry.AtomId);
            if (!baseline.TryGetFile(receiptPath, out _))
            {
                throw new InvalidOperationException(
                    $"atom {entry.AtomId} has no baseline formalization receipt: {receiptPath}");
            }

            var receipt = DigestionFormalizationReceipt.LoadTrusted(baseline, receiptPath);
            if (!string.Equals(receipt.AtomId, entry.AtomId, StringComparison.Ordinal))
            {
                throw new InvalidOperationException(
                    $"atom {entry.AtomId} baseline formalization receipt has a different atom_id");
            }

            var signatures = receipt.HostedExtensions.ToDictionary(
                static extension => extension.Gid,
                static extension => extension.Signature,
                StringComparer.Ordinal);
            signatures.Add(receipt.PrimaryGid, receipt.Signature);
            foreach (var gidText in entry.CoverageGids)
            {
                if (!signatures.TryGetValue(gidText, out var baselineSignature))
                {
                    throw new InvalidOperationException(
                        $"atom {entry.AtomId} baseline formalization receipt does not pin {gidText}");
                }

                if (!Gid.TryParse(gidText, out var gid))
                {
                    throw new InvalidOperationException(
                        $"atom {entry.AtomId} coverage GID is invalid: {gidText}");
                }

                var currentSignature = DigestionFormalizationReceipt.ResolveSignature(gid, currentReport);
                if (currentSignature != baselineSignature)
                {
                    throw new InvalidOperationException(
                        $"atom {entry.AtomId} Lean declaration signature changed for {gidText}");
                }
            }
        }
    }

    internal static void RequireFinalReceiptRealignmentFullScan(
        BackfillInventoryDocument finalDocument,
        RepositorySnapshot finalSnapshot,
        AcceptedLeanClosure lean,
        VerifiedScribeEmissions verified,
        BackfillInventoryDocument baselineDocument,
        RepositorySnapshot baselineSnapshot)
    {
        var finalEvaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            finalDocument,
            finalSnapshot,
            lean,
            verified,
            baselineDocument,
            baselineSnapshot: baselineSnapshot);
        RequireNoReceiptIntegrityFailure(finalEvaluation);
    }

    private static string ParseRealignArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 2
            && arguments[0] == "--base"
            && !string.IsNullOrWhiteSpace(arguments[1]))
        {
            return arguments[1];
        }

        throw new InvalidOperationException("USAGE: StrataLint realign-receipts --base REV");
    }

    internal static void RequireNoReceiptIntegrityFailure(
        DigestionLedgerEvaluation evaluation)
    {
        if (evaluation.HasReceiptIntegrityFailure)
        {
            throw new InvalidOperationException(
                "digest status is invalid: "
                + string.Join("; ", evaluation.ReceiptIntegrityFailureReasons));
        }
    }

    private sealed class ReceiptRealignmentCounts
    {
        internal int CoverageReceiptsChanged { get; set; }

        internal int ScribeReceiptsChanged { get; set; }

        internal int EntriesChanged { get; set; }
    }
}
