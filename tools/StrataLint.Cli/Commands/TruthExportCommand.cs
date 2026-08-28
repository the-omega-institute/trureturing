using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;
using Trureturing.Truth;

namespace StrataLint.Cli;

/// Exports the strict active frozen truth from one immutable Git revision and one explicit Lean report.
/// The report's source bindings are checked against the resolved revision; the truth-export wire carries
/// only the immutable commit and tree identities.
internal static class TruthExportCommand
{
    private const string FileName = "truth-export.v1.json";

    internal static ExplicitCommandResult Run(
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        if (!TryParseArguments(arguments, out var options))
        {
            return Usage();
        }

        try
        {
            var identity = DagLedgerCommandPreparation.Ask(repository.ResolveCurrentRevision);
            var snapshot = Decode(DagLedgerCommandPreparation.Ask(
                () => repository.ReadRevision(identity.Revision)));
            var report = RawLeanReportArtifact.ReadFile(options.CandidateLeanReport, snapshot);
            var preparation = PrepareStrictHistory(repository, snapshot, identity, report);
            if (preparation.Outcome is FrozenLedgerValidationOutcome.Rejected rejected)
            {
                return new ExplicitCommandResult(
                    2,
                    string.Empty,
                    $"TRUTH_EXPORT_REJECTED {rejected.Message}\n");
            }

            var accepted = (FrozenLedgerValidationOutcome.Accepted)preparation.Outcome;
            var model = TruthExportProjection.Project(
                accepted.Capability.ActiveFrozenNodes,
                identity.Revision,
                Bare(identity.TreeOid));
            var finalPath = WriteAtomically(options.OutDirectory, model);
            return new ExplicitCommandResult(
                0,
                $"TRUTH_EXPORT nodes={model.Nodes.Length} "
                    + $"source_commit={model.SourceCommit} out={finalPath}\n",
                string.Empty);
        }
        catch (Exception exception) when (
            exception is DagLedgerCommandPreparation.RepositoryUnavailableException
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

    internal static StrictTruthHistoryPreparation PrepareStrictHistory(
        IRepositoryGateway repository,
        RepositorySnapshot snapshot,
        FrozenRevisionIdentity identity,
        LeanAxiomReport report)
    {
        var ledgerFiles = LedgerFiles(snapshot);
        var baseView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            ledgerFiles.ToImmutableDictionary(static file => file.Path)));
        var truth = DagLedgerCommandPreparation.BuildTruth(snapshot, report);
        var states = LeanTruthStates.Resolve(truth.Snapshot, truth.Lean);
        var adjacency = LeanImportAdjacency.Build(truth.Snapshot, truth.Lean);
        var catalog = DagLedgerCommandPreparation.BuildCompleteCatalog(
            truth.Snapshot,
            truth.Lean,
            states,
            adjacency,
            baseView,
            identity);
        var events = DagLedgerCommandPreparation.LoadTrustedLedgerFiles(
            ledgerFiles,
            "frozen ledger");
        _ = TrustReferences(repository, events);
        var outcome = FrozenLedger.ValidateTrustedHistory(baseView, catalog);
        return new StrictTruthHistoryPreparation(truth, states, baseView, outcome);
    }

    private static ImmutableArray<RepositoryFile> LedgerFiles(RepositorySnapshot snapshot)
    {
        var prefix = FrozenLedgerChangeClassifier.AcceptedRoot + "/";
        var files = snapshot.Files.Values
            .Where(file => file.Path.Value.StartsWith(prefix, StringComparison.Ordinal)
                && file.Path.Value.EndsWith(".json", StringComparison.Ordinal)
                && !file.Path.Value[prefix.Length..].Contains('/', StringComparison.Ordinal))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        return files.IsEmpty
            ? throw new InvalidOperationException(
                $"immutable revision contains no frozen ledger files under {FrozenLedgerChangeClassifier.AcceptedRoot}")
            : files;
    }

    private static TrustedFrozenGitReferences TrustReferences(
        IRepositoryGateway repository,
        ImmutableArray<DagLedgerFileEvent> events)
    {
        var references = FrozenLedger.ScanReferences(events) switch
        {
            FrozenLedgerReferenceScanOutcome.Accepted accepted => accepted.References,
            FrozenLedgerReferenceScanOutcome.Rejected rejected => throw new InvalidOperationException(
                "frozen ledger references are invalid: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown ledger reference scan outcome"),
        };
        return references.CommitOids.IsEmpty
            && references.TreeOids.IsEmpty
            && references.BlobOids.IsEmpty
                ? TrustedFrozenGitReferences.CreateForTrustedAdapter([])
                : repository.ValidateFrozenReferences(references);
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(
                "immutable revision snapshot is invalid: " + failure.Message),
        };

    private static string WriteAtomically(string outDirectory, TruthExportModel model)
    {
        var bytes = TruthExportJsonWriter.Write(model);
        Directory.CreateDirectory(outDirectory);
        var finalPath = Path.Combine(outDirectory, FileName);
        var temporaryPath = Path.Combine(outDirectory, $"{FileName}.{Guid.NewGuid():N}.tmp");
        try
        {
            File.WriteAllBytes(temporaryPath, bytes.AsSpan());
            var written = File.ReadAllBytes(temporaryPath);
            var roundTripped = TruthExportJsonWriter.Write(TruthExportJsonReader.Read(written));
            if (!written.AsSpan().SequenceEqual(bytes.AsSpan())
                || !roundTripped.AsSpan().SequenceEqual(bytes.AsSpan()))
            {
                throw new IOException(
                    "written truth export bytes are not byte-identical after canonical round-trip.");
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

    private static bool TryParseArguments(
        IReadOnlyList<string> arguments,
        out TruthExportArguments options)
    {
        options = default;
        if (arguments.Count != 4)
        {
            return false;
        }

        string? outDirectory = null;
        string? candidateLeanReport = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            var value = arguments[index + 1];
            if (string.IsNullOrWhiteSpace(value))
            {
                return false;
            }

            switch (arguments[index])
            {
                case "--out" when outDirectory is null:
                    outDirectory = value;
                    break;
                case "--candidate-lean-report" when candidateLeanReport is null:
                    candidateLeanReport = value;
                    break;
                default:
                    return false;
            }
        }

        if (outDirectory is null || candidateLeanReport is null)
        {
            return false;
        }

        options = new TruthExportArguments(outDirectory, candidateLeanReport);
        return true;
    }

    private static ExplicitCommandResult Usage() => new(
        1,
        string.Empty,
        "USAGE: StrataLint truth-export --out DIR --candidate-lean-report FILE\n");

    private readonly record struct TruthExportArguments(
        string OutDirectory,
        string CandidateLeanReport);
}

internal sealed record StrictTruthHistoryPreparation(
    TruthContext Truth,
    ImmutableDictionary<RepoPath, TruthState> States,
    FrozenLedgerBaseView BaseView,
    FrozenLedgerValidationOutcome Outcome);
