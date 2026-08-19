using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

/// `truth-export --out <dir>` writes the base's STRICT-accepted active frozen truth to a single
/// canonical file `<dir>/truth-export.v1.json`.
///
/// The exported nodes come DIRECTLY from the strict validation outcome: the command gathers the
/// same inputs admission gathers (snapshot -> Lean closure -> DAG -> a COMPLETE frozen catalog,
/// the full linear ledger syntax, and repository-validated Git references over the whole ledger),
/// then calls the strict FrozenLedger.ValidateHistory (requireCompleteCatalog=true,
/// allowPendingReattestation=false). On Accepted it exports Accepted.Capability.ActiveFrozenNodes;
/// on Rejected -- or any gathering fault -- it fails closed with a non-zero exit and writes no
/// file. The guard and the exported object are the SAME strict ActiveFrozenNodes: there is no
/// separate prefix baseline and no boolean guard over a weaker view.
internal static class TruthExportCommand
{
    internal static ExplicitCommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(arguments);
        if (arguments.Count != 2 || arguments[0] != "--out" || string.IsNullOrWhiteSpace(arguments[1]))
        {
            return Usage();
        }

        var outDirectory = arguments[1];
        try
        {
            var outcome = ValidateStrictHistory(
                repositoryRoot,
                repository,
                leanReportSource,
                out var currentIdentity);
            if (outcome is FrozenLedgerValidationOutcome.Rejected rejected)
            {
                return new ExplicitCommandResult(
                    2,
                    string.Empty,
                    $"TRUTH_EXPORT_REJECTED {rejected.Message}\n");
            }

            var accepted = (FrozenLedgerValidationOutcome.Accepted)outcome;
            var model = TruthExportModel.Create(
                accepted.Capability.ActiveFrozenNodes,
                currentIdentity.Revision,
                Bare(currentIdentity.TreeOid));
            var finalPath = WriteAtomically(outDirectory, model);
            return new ExplicitCommandResult(
                0,
                $"TRUTH_EXPORT nodes={model.Nodes.Length} "
                    + $"source_commit={model.SourceCommit} out={finalPath}\n",
                string.Empty);
        }
        catch (Exception exception) when (
            exception is DagLedgerCommandPreparation.RepositoryUnavailableException
                or DagLedgerCommandPreparation.LeanReportUnusableException
                or InvalidOperationException
                or FormatException
                or ArgumentException
                or JsonException
                or IOException
                or UnauthorizedAccessException)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"TRUTH_EXPORT_INVALID {exception.Message}\n");
        }
    }

    /// Gathers the three strict-validation inputs from the base's own owners and runs the strict
    /// FrozenLedger.ValidateHistory. The catalog is the COMPLETE Closed set (not the writer
    /// catalog's candidate scope) and the references are validated over the WHOLE ledger, so the
    /// verdict is admission-grade.
    private static FrozenLedgerValidationOutcome ValidateStrictHistory(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        out FrozenRevisionIdentity currentIdentity)
    {
        var ledgerDirectory = Path.Combine(
            repositoryRoot,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
        var baselineFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(ledgerDirectory);
        var baseView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            baselineFiles.ToImmutableDictionary(static file => file.Path)));
        var truth = DagLedgerCommandPreparation.BuildTruth(repository, leanReportSource);
        currentIdentity = DagLedgerCommandPreparation.Ask(repository.ResolveCurrentRevision);
        var catalog = DagLedgerCommandPreparation.BuildCompleteCatalog(
            truth.Snapshot,
            truth.Lean,
            truth.Dag,
            baseView,
            currentIdentity);
        var syntax = DagLedgerCommandPreparation.LoadLedgerFiles(baselineFiles, "frozen ledger");
        var trustedReferences = TrustReferences(repository, syntax);
        return FrozenLedger.ValidateHistory(syntax, catalog, trustedReferences);
    }

    private static TrustedFrozenGitReferences TrustReferences(
        IRepositoryGateway repository,
        FrozenLedgerSyntax syntax)
    {
        var references = FrozenLedger.ScanReferences(syntax) switch
        {
            FrozenLedgerReferenceScanOutcome.Accepted accepted => accepted.References,
            FrozenLedgerReferenceScanOutcome.Rejected rejected => throw new InvalidOperationException(
                "frozen ledger references are invalid: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown ledger reference scan outcome"),
        };
        return references.CommitOids.IsEmpty
            && references.TreeOids.IsEmpty
            && references.BlobOids.IsEmpty
            && references.EnvironmentReferences.IsEmpty
                ? TrustedFrozenGitReferences.CreateForTrustedAdapter([], [])
                : repository.ValidateFrozenReferences(references);
    }

    /// PIN 3: same-directory temp file -> full write -> self-read + schema/dialect round-trip
    /// validation of the just-written bytes -> atomic rename. On any failure the temp file is
    /// removed and no partial or stale final file remains.
    private static string WriteAtomically(string outDirectory, TruthExportModel model)
    {
        var bytes = TruthExportJsonWriter.Write(model);
        Directory.CreateDirectory(outDirectory);
        var fileName = Path.GetFileName(TruthExportModel.RelativePath);
        var finalPath = Path.Combine(outDirectory, fileName);
        var temporaryPath = Path.Combine(
            outDirectory,
            $"{fileName}.{Guid.NewGuid():N}.tmp");
        try
        {
            File.WriteAllBytes(temporaryPath, bytes.AsSpan());
            var written = File.ReadAllBytes(temporaryPath);
            _ = TruthExportJsonReader.Read(written);
            if (!written.AsSpan().SequenceEqual(bytes.AsSpan()))
            {
                throw new IOException("written truth export bytes are not byte-identical to the model.");
            }

            File.Move(temporaryPath, finalPath, overwrite: true);
            return finalPath;
        }
        catch
        {
            if (File.Exists(temporaryPath))
            {
                File.Delete(temporaryPath);
            }

            throw;
        }
    }

    private static string Bare(string taggedOid)
    {
        var separator = taggedOid.IndexOf(':', StringComparison.Ordinal);
        return separator < 0 ? taggedOid : taggedOid[(separator + 1)..];
    }

    private static ExplicitCommandResult Usage() => new(
        1,
        string.Empty,
        "USAGE: StrataLint truth-export --out DIR\n");
}
