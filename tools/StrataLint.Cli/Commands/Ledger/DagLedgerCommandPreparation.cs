using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record DagLedgerCommandContext(
    string LedgerPath,
    ImmutableArray<RepositoryFile> BaselineFiles,
    FrozenLedgerConsistent Baseline,
    FrozenLedgerBaseView BaseView,
    FrozenMaterialCatalog Catalog,
    LeanAxiomReport Report,
    RepositorySnapshot Snapshot);

internal sealed record DagLedgerCandidateMaterial(
    string LedgerPath,
    FrozenLedgerBaseView BaseView,
    ImmutableArray<RepositoryFile> BaselineFiles,
    FrozenMaterialCatalog Catalog,
    LeanAxiomReport Report,
    RawChangeSet Changes,
    RepositorySnapshot Snapshot);

internal static class DagLedgerCommandPreparation
{
    internal static DagLedgerCommandContext Prepare(
        string repositoryRoot,
        IRepositoryGateway repository,
        string candidateLeanReport,
        string? changeBase = null,
        ImmutableArray<RepositoryFile> trustedBaselineFiles = default) =>
        Prepare(
            repositoryRoot,
            repository,
            new FileLeanReportSource(candidateLeanReport),
            changeBase,
            trustedBaselineFiles);

    /// Same preparation, with the raw report supplied by the caller rather than read from a path.
    /// Callers that already hold an ILeanReportSource (the CLI environment does) get the
    /// authoritative FrozenLedgerConsistent without a second copy of this assembly line.
    ///
    /// changeBase is optional and defaults to null, which preserves the original behaviour byte
    /// for byte: the change set still comes from repository.ReadCurrentChanges() (uncommitted
    /// working-tree delta against HEAD). Passing a revision switches the change set to that
    /// revision's delta against the working tree instead (repository.ReadChanges(changeBase)),
    /// which is what lets a caller match `make gate BASE=<rev>`'s committed-delta view (issue
    /// #2474: a change that is already committed reads as empty against ReadCurrentChanges alone).
    internal static DagLedgerCommandContext Prepare(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        string? changeBase = null,
        ImmutableArray<RepositoryFile> trustedBaselineFiles = default)
    {
        var candidate = PrepareCandidate(
            repositoryRoot,
            repository,
            leanReportSource,
            changeBase,
            trustedBaselineFiles);
        var baseline = candidate.BaseView.ToWriterBaseline();
        return new DagLedgerCommandContext(
            candidate.LedgerPath,
            candidate.BaselineFiles,
            baseline,
            candidate.BaseView,
            candidate.Catalog,
            candidate.Report,
            candidate.Snapshot);
    }

    internal static DagLedgerCandidateMaterial PrepareCandidate(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        string? changeBase = null,
        ImmutableArray<RepositoryFile> trustedBaselineFiles = default)
    {
        var ledgerPath = Path.Combine(
            repositoryRoot,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
        var baselineFiles = ReadLedgerDirectoryFiles(ledgerPath);
        var trustedFiles = trustedBaselineFiles.IsDefault
            ? baselineFiles
            : trustedBaselineFiles;
        var baseView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            trustedFiles.ToImmutableDictionary(static file => file.Path)));
        var truth = BuildLeanTruth(repository, leanReportSource);
        var snapshot = truth.Snapshot;
        var report = truth.Report;
        var lean = truth.Lean;
        var changes = changeBase is null
            ? Ask(repository.ReadCurrentChanges)
            : Ask(() => repository.ReadChanges(changeBase));
        var catalog = BuildWriterCatalog(
            snapshot,
            lean,
            baseView,
            changes,
            Ask(repository.ResolveCurrentRevision));

        return new DagLedgerCandidateMaterial(
            ledgerPath,
            baseView,
            baselineFiles,
            catalog,
            report,
            changes,
            snapshot);
    }

    /// Reads the repository, validates the Lean closure and builds the truth DAG -- the part of
    /// Prepare that any DAG consumer needs, without the frozen-ledger work. Callers that only want
    /// the graph (the DAG projection command) share this assembly line rather than growing a
    /// second, drifting copy of it.
    /// Builds complete current material for the canonical writer. Coordinate-only drift is itself
    /// writer input, so ledger-append cannot restrict this catalog to source-affected paths.
    internal static FrozenMaterialCatalog BuildWriterCatalog(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        FrozenLedgerBaseView baseView,
        RawChangeSet changes,
        FrozenRevisionIdentity currentIdentity)
    {
        _ = baseView;
        _ = changes;
        _ = currentIdentity;
        var states = LeanTruthStates.Resolve(snapshot, lean);
        var adjacency = LeanImportAdjacency.Build(snapshot, lean);
        return FrozenContentAddress.Build(snapshot, lean, states, adjacency) switch
        {
            FrozenMaterialOutcome.Accepted accepted => accepted.Capability,
            FrozenMaterialOutcome.Rejected rejected => throw new InvalidOperationException(
                "writer frozen catalog build failed: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown frozen material outcome"),
        };
    }

    internal static FrozenMaterialCatalog BuildAdmissionCatalog(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        ImmutableDictionary<RepoPath, TruthState> states,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency,
        FrozenLedgerBaseView baseView,
        FrozenLedgerAdmissionScope scope,
        FrozenRevisionIdentity currentIdentity)
    {
        _ = currentIdentity;
        return FrozenContentAddress.BuildAdmissionCatalog(
            snapshot,
            lean,
            states,
            adjacency,
            scope.Paths,
            baseView.ActiveByPath.ToDictionary(
                static item => item.Key,
                static item => item.Value.Material));
    }

    /// Builds material for every Closed module. Strict read-model consumers need the complete
    /// catalog so ValidateHistory can reconcile the entire active frozen set, not only a changed
    /// candidate scope.
    internal static FrozenMaterialCatalog BuildCompleteCatalog(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        ImmutableDictionary<RepoPath, TruthState> states,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency,
        FrozenLedgerBaseView baseView,
        FrozenRevisionIdentity currentIdentity)
    {
        _ = baseView;
        _ = currentIdentity;
        return FrozenContentAddress.Build(snapshot, lean, states, adjacency) switch
        {
            FrozenMaterialOutcome.Accepted accepted => accepted.Capability,
            FrozenMaterialOutcome.Rejected rejected => throw new InvalidOperationException(
                "complete frozen catalog build failed: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown frozen material outcome"),
        };
    }

    internal static TruthContext BuildTruth(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource)
    {
        var snapshot = Decode(Ask(repository.ReadCurrent));
        var (report, lean) = LoadLean(snapshot, leanReportSource);
        return BuildTruth(snapshot, report, lean);
    }

    private static TruthContext BuildLeanTruth(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource)
    {
        var snapshot = Decode(Ask(repository.ReadCurrent));
        var (report, lean) = LoadLean(snapshot, leanReportSource);
        return new TruthContext(snapshot, lean, report);
    }

    internal static TruthContext BuildTruth(
        RepositorySnapshot snapshot,
        LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(report);
        return BuildTruth(snapshot, report, ValidateLean(snapshot, report));
    }

    private static TruthContext BuildTruth(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        AcceptedLeanClosure lean)
        => new(snapshot, lean, report);

    private static (LeanAxiomReport Report, AcceptedLeanClosure Lean) LoadLean(
        RepositorySnapshot snapshot,
        ILeanReportSource leanReportSource)
    {
        // Loading and validating the report are one step from a caller's point of view: both
        // failures say the build artefact is unusable, not that this repository is wrong. Keeping
        // them together lets a caller classify them as one thing.
        LeanAxiomReport report;
        AcceptedLeanClosure lean;
        try
        {
            report = leanReportSource.Load(snapshot);
            lean = ValidateLean(snapshot, report);
        }
        catch (Exception exception) when (exception is not LeanReportUnusableException)
        {
            throw new LeanReportUnusableException(exception);
        }

        return (report, lean);
    }

    /// Runs a gateway call that reads repository state, marking anything it throws. A repository
    /// that cannot be read is a fault in the environment, not a statement about the frozen ledger,
    /// and callers classifying failures cannot tell the two apart otherwise -- both arrive as
    /// IOException or InvalidOperationException. Reference validation is not routed through here:
    /// its refusals are about the ledger's contents.
    internal static T Ask<T>(Func<T> gatewayCall)
    {
        try
        {
            return gatewayCall();
        }
        catch (Exception exception) when (exception is not RepositoryUnavailableException)
        {
            throw new RepositoryUnavailableException(exception);
        }
    }

    /// Raised when a gateway call fails. Never escapes a classifying caller: the original is
    /// rethrown in its place.
    internal sealed class RepositoryUnavailableException(Exception inner)
        : Exception("repository could not be read", inner);

    /// Raised when the raw Lean report cannot be loaded or does not validate. Both are faults in
    /// a build artefact rather than statements about the repository, and callers that classify
    /// failures need to tell them apart from ledger faults -- which otherwise arrive as the same
    /// exception types.
    internal sealed class LeanReportUnusableException(Exception inner)
        : Exception("raw Lean report is unusable", inner);

    private sealed class FileLeanReportSource(string path) : ILeanReportSource
    {
        public LeanAxiomReport Load(RepositorySnapshot snapshot) =>
            RawLeanReportArtifact.ReadFile(path, snapshot);
    }

    internal static ImmutableArray<DagLedgerFileEvent> LoadLedgerDirectory(
        string directory,
        string label) =>
        LoadLedgerFiles(ReadLedgerDirectoryFiles(directory), label);

    internal static ImmutableArray<RepositoryFile> ReadLedgerDirectoryFiles(string directory) =>
        Directory.EnumerateFiles(directory, "*.json")
            .Select(path => CreateLedgerRepositoryFile(
                path,
                ImmutableArray.CreateRange(File.ReadAllBytes(path))))
            .ToImmutableArray();

    internal static RepositoryFile CreateLedgerRepositoryFile(
        string path,
        ImmutableArray<byte> bytes) =>
        new(
            RepoPath.CreateKnown(
                $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{Path.GetFileName(path)}"),
            bytes,
            Encoding.UTF8.GetString(bytes.AsSpan()));

    internal static ImmutableArray<DagLedgerFileEvent> LoadLedgerFiles(
        IEnumerable<RepositoryFile> files,
        string label) =>
        LoadLedgerFiles(files, label, trustRecordedHashes: false);

    internal static ImmutableArray<DagLedgerFileEvent> LoadTrustedLedgerFiles(
        IEnumerable<RepositoryFile> files,
        string label) =>
        LoadLedgerFiles(files, label, trustRecordedHashes: true);

    private static ImmutableArray<DagLedgerFileEvent> LoadLedgerFiles(
        IEnumerable<RepositoryFile> files,
        string label,
        bool trustRecordedHashes)
    {
        var events = (trustRecordedHashes
            ? DagLedgerLoader.LoadTrustedFiles(files)
            : DagLedgerLoader.LoadFiles(files)) switch
        {
            DagLedgerFilesLoadOutcome.Loaded loaded => loaded.Events,
            DagLedgerFilesLoadOutcome.Invalid invalid => throw new InvalidOperationException(
                label + " syntax is invalid: " + invalid.Message),
            _ => throw new InvalidOperationException("unknown ledger files load outcome"),
        };
        var orderedSuccessfully = trustRecordedHashes
            ? DagLedgerLoader.TryOrderTrustedHistory(events, out var ordered)
            : DagLedgerLoader.TryOrderClosedDag(
                events,
                ImmutableArray<string>.Empty,
                out ordered);
        if (!orderedSuccessfully)
        {
            throw new InvalidOperationException(label + " does not form a closed dependency DAG");
        }

        return ordered;
    }

    internal static ImmutableArray<DagLedgerFileEvent> ValidateGeneratedEventFiles(
        FrozenLedgerBaseView baseView,
        ImmutableArray<RepositoryFile> files,
        string label)
    {
        var events = DagLedgerLoader.LoadFiles(files) switch
        {
            DagLedgerFilesLoadOutcome.Loaded loaded => loaded.Events,
            DagLedgerFilesLoadOutcome.Invalid invalid => throw new InvalidOperationException(
                label + " syntax is invalid: " + invalid.Message),
            _ => throw new InvalidOperationException("unknown ledger files load outcome"),
        };
        if (!DagLedgerLoader.TryOrderIncrementalDag(
                events,
                baseView.EventIdentities,
                baseView.EventHashes,
                out var ordered))
        {
            throw new InvalidOperationException(
                label + " does not extend the trusted frozen-ledger dependency DAG");
        }

        return ordered;
    }

    /// Bytes that will not decode are a fault in the repository we were handed, not a verdict about
    /// its ledger -- spec A16 classifies snapshot rejection as infrastructure. The read itself can
    /// succeed here, so marking only the gateway call would leave this failure to arrive as an
    /// ordinary InvalidOperationException and be reported as a ledger fault. The decode message is
    /// kept as the inner exception so callers can still name the cause.
    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new RepositoryUnavailableException(new InvalidOperationException(failure.Message)),
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
