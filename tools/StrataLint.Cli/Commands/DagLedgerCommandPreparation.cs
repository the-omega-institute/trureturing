using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record DagLedgerCommandContext(
    string LedgerPath,
    byte[] BaselineBytes,
    ImmutableArray<RepositoryFile> BaselineFiles,
    FrozenLedgerSyntax BaselineSyntax,
    FrozenLedgerConsistent Baseline,
    FrozenLedgerBaseView BaseView,
    FrozenMaterialCatalog Catalog,
    LeanAxiomReport Report,
    RepositorySnapshot Snapshot);

internal sealed record DagLedgerCandidateMaterial(
    string LedgerPath,
    byte[] BaselineBytes,
    FrozenLedgerSyntax BaselineSyntax,
    FrozenLedgerBaseView BaseView,
    ImmutableArray<RepositoryFile> BaselineFiles,
    FrozenMaterialCatalog Catalog,
    LeanAxiomReport Report,
    RepositorySnapshot Snapshot);

internal sealed record TruthContext(
    RepositorySnapshot Snapshot,
    AcceptedLeanClosure Lean,
    LeanAxiomReport Report,
    AcyclicTruthDag Dag);

internal static class DagLedgerCommandPreparation
{
    internal static DagLedgerCommandContext Prepare(
        string repositoryRoot,
        IRepositoryGateway repository,
        string candidateLeanReport) =>
        Prepare(repositoryRoot, repository, new FileLeanReportSource(candidateLeanReport));

    /// Same preparation, with the raw report supplied by the caller rather than read from a path.
    /// Callers that already hold an ILeanReportSource (the CLI environment does) get the
    /// authoritative FrozenLedgerConsistent without a second copy of this assembly line.
    internal static DagLedgerCommandContext Prepare(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource)
    {
        var candidate = PrepareCandidate(repositoryRoot, repository, leanReportSource);
        var baseline = candidate.BaseView.ToWriterBaseline(candidate.BaselineSyntax);
        return new DagLedgerCommandContext(
            candidate.LedgerPath,
            candidate.BaselineBytes,
            candidate.BaselineFiles,
            candidate.BaselineSyntax,
            baseline,
            candidate.BaseView,
            candidate.Catalog,
            candidate.Report,
            candidate.Snapshot);
    }

    internal static DagLedgerCandidateMaterial PrepareCandidate(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource)
    {
        var ledgerPath = Path.Combine(
            repositoryRoot,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
        var baselineFiles = ReadLedgerDirectoryFiles(ledgerPath);
        var baseView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            baselineFiles.ToImmutableDictionary(static file => file.Path)));
        var baselineSyntax = LoadTrustedLedgerFiles(baseView, "existing frozen ledger");
        var baselineBytes = baselineSyntax.RawBytes.ToArray();
        var truth = BuildTruth(repository, leanReportSource);
        var snapshot = truth.Snapshot;
        var report = truth.Report;
        var lean = truth.Lean;
        var dag = truth.Dag;
        var catalog = BuildCatalog(
            snapshot,
            lean,
            dag,
            baselineSyntax,
            Ask(repository.ResolveCurrentRevision));

        return new DagLedgerCandidateMaterial(
            ledgerPath,
            baselineBytes,
            baselineSyntax,
            baseView,
            baselineFiles,
            catalog,
            report,
            snapshot);
    }

    /// Reads the repository, validates the Lean closure and builds the truth DAG -- the part of
    /// Prepare that any DAG consumer needs, without the frozen-ledger work. Callers that only want
    /// the graph (the DAG projection command) share this assembly line rather than growing a
    /// second, drifting copy of it.
    /// The frozen material catalog for a snapshot. Prepare needs it for the writer path and the
    /// admission final-state gate needs it for the read-only path; they share this one assembly
    /// line rather than growing a second, drifting copy of the attestation algebra.
    internal static FrozenMaterialCatalog BuildCatalog(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        AcyclicTruthDag dag,
        FrozenLedgerSyntax ledgerSyntax,
        FrozenRevisionIdentity currentIdentity)
    {
        var environment = BuildEnvironment(snapshot, ledgerSyntax);
        if (currentIdentity.CommitOid.StartsWith("git-sha256:", StringComparison.Ordinal)
            != environment.OriginCommitOid.StartsWith("git-sha256:", StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                "current revision and frozen Genesis use different Git hash algorithms");
        }

        var algorithm = environment.OriginCommitOid.StartsWith("git-sha256:", StringComparison.Ordinal)
            ? HashAlgorithmName.SHA256
            : HashAlgorithmName.SHA1;
        var attestations = dag.Nodes
            .Where(static node => node.State is TruthState.Closed && node.ModuleName is not null)
            .Select(node => new FrozenModuleAttestation(
                node.RepoPath,
                FrozenContentAddress.ComputeGitBlobOid(
                    snapshot.Files[node.RepoPath].RawBytes.AsSpan(),
                    algorithm))
            {
                BaseCommitOid = currentIdentity.CommitOid,
                BaseTreeOid = currentIdentity.TreeOid,
            })
            .ToImmutableArray();
        return FrozenContentAddress.Build(snapshot, lean, dag, environment, attestations) switch
        {
            FrozenMaterialOutcome.Accepted accepted => accepted.Capability,
            FrozenMaterialOutcome.Rejected rejected => throw new InvalidOperationException(rejected.Message),
            _ => throw new InvalidOperationException("unknown frozen material outcome"),
        };
    }

    internal static FrozenMaterialCatalog BuildAdmissionCatalog(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        AcyclicTruthDag dag,
        FrozenLedgerBaseView baseView,
        FrozenLedgerAdmissionScope scope,
        FrozenRevisionIdentity currentIdentity)
    {
        var environment = BuildEnvironment(
            snapshot,
            baseView.Origin.CommitOid,
            baseView.Origin.TreeOid);
        if (currentIdentity.CommitOid.StartsWith("git-sha256:", StringComparison.Ordinal)
            != environment.OriginCommitOid.StartsWith("git-sha256:", StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                "current revision and frozen Genesis use different Git hash algorithms");
        }

        var algorithm = environment.OriginCommitOid.StartsWith("git-sha256:", StringComparison.Ordinal)
            ? HashAlgorithmName.SHA256
            : HashAlgorithmName.SHA1;
        var attestations = dag.Nodes
            .Where(node => node.State is TruthState.Closed
                && node.ModuleName is not null
                && scope.Paths.Contains(node.RepoPath))
            .Select(node => new FrozenModuleAttestation(
                node.RepoPath,
                FrozenContentAddress.ComputeGitBlobOid(
                    snapshot.Files[node.RepoPath].RawBytes.AsSpan(),
                    algorithm))
            {
                BaseCommitOid = currentIdentity.CommitOid,
                BaseTreeOid = currentIdentity.TreeOid,
            })
            .ToImmutableArray();
        return FrozenContentAddress.BuildAdmissionCatalog(
            snapshot,
            lean,
            dag,
            environment,
            attestations,
            scope.Paths,
            baseView.ActiveByPath.ToDictionary(
                static item => item.Key,
                static item => item.Value.Material));
    }

    internal static TruthContext BuildTruth(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource)
    {
        var snapshot = Decode(Ask(repository.ReadCurrent));
        var (report, lean) = LoadLean(snapshot, leanReportSource);
        var dag = AcyclicTruthDag.Build(snapshot, lean) switch
        {
            DagBuildOutcome.Accepted accepted => accepted.Capability,
            DagBuildOutcome.Rejected rejected => throw new InvalidOperationException(
                "candidate truth DAG is cyclic: "
                + string.Join(" -> ", rejected.Witness.Select(static path => path.Value))),
            _ => throw new InvalidOperationException("unknown truth DAG outcome"),
        };
        return new TruthContext(snapshot, lean, report, dag);
    }

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

    internal static FrozenLedgerSyntax LoadLedger(ReadOnlySpan<byte> bytes, string label) =>
        DagLedgerLoader.Load(bytes) switch
        {
            DagLedgerLoadOutcome.Loaded loaded => loaded.Syntax,
            DagLedgerLoadOutcome.Invalid invalid => throw new InvalidOperationException(
                label + " syntax is invalid: " + invalid.Message),
            _ => throw new InvalidOperationException("unknown ledger load outcome"),
        };

    internal static FrozenLedgerSyntax LoadLedgerDirectory(string directory, string label) =>
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

    internal static FrozenLedgerSyntax LoadLedgerFiles(
        IEnumerable<RepositoryFile> files,
        string label)
    {
        var events = DagLedgerLoader.LoadFiles(files) switch
        {
            DagLedgerFilesLoadOutcome.Loaded loaded => loaded.Events,
            DagLedgerFilesLoadOutcome.Invalid invalid => throw new InvalidOperationException(
                label + " syntax is invalid: " + invalid.Message),
            _ => throw new InvalidOperationException("unknown ledger files load outcome"),
        };
        if (!DagLedgerLoader.TryOrderClosedDag(
                events,
                ImmutableArray<string>.Empty,
                out var ordered))
        {
            throw new InvalidOperationException(label + " does not form a closed dependency DAG");
        }

        return DagLedgerLoader.ToLinearSyntax(OrderForReplay(ordered));
    }

    internal static FrozenLedgerSyntax LoadTrustedLedgerFiles(
        FrozenLedgerBaseView baseView,
        string label)
    {
        ArgumentNullException.ThrowIfNull(baseView);
        var events = baseView.Events.Select(static item => new DagLedgerFileEvent(
            item.SourcePath,
            item.Identity,
            item.EventHash,
            item.EventType,
            item.Payload,
            item.SchemaVersion,
            new FrozenLedgerLineSyntax(item.RawBytes, item.Root, item.EventHash),
            Input: null)).ToImmutableArray();
        if (!DagLedgerLoader.TryOrderClosedDag(
                events,
                ImmutableArray<string>.Empty,
                out var ordered))
        {
            throw new InvalidOperationException(
                label + " cannot be projected into the writer's linear event order");
        }

        return DagLedgerLoader.ToLinearSyntax(OrderForReplay(ordered));
    }

    internal static FrozenLedgerSyntax LoadTrustedLedgerWithSuffix(
        FrozenLedgerBaseView baseView,
        ImmutableArray<RepositoryFile> suffixFiles,
        string label)
    {
        ArgumentNullException.ThrowIfNull(baseView);
        var suffix = ValidateGeneratedEventFiles(baseView, suffixFiles, label);
        var events = baseView.Events.Select(static item => new DagLedgerFileEvent(
                item.SourcePath,
                item.Identity,
                item.EventHash,
                item.EventType,
                item.Payload,
                item.SchemaVersion,
                new FrozenLedgerLineSyntax(item.RawBytes, item.Root, item.EventHash),
                Input: null))
            .Concat(suffix)
            .OrderBy(static item => item.Identity, StringComparer.Ordinal)
            .ToImmutableArray();
        return DagLedgerLoader.ToLinearSyntax(OrderForReplay(events));
    }

    private static ImmutableArray<DagLedgerFileEvent> OrderForReplay(
        ImmutableArray<DagLedgerFileEvent> events)
    {
        var remaining = events.ToList();
        var result = ImmutableArray.CreateBuilder<DagLedgerFileEvent>(events.Length);
        var identities = new HashSet<string>(StringComparer.Ordinal);
        var hashes = new HashSet<string>(StringComparer.Ordinal);
        while (remaining.Count > 0)
        {
            var index = remaining.FindIndex(item => item.EventType switch
            {
                "Genesis" => result.Count == 0,
                "Freeze" => result.Count > 0
                    && DependenciesPresent(item.Payload, "prerequisite_frozen_node_ids", identities),
                "Reattest" => item.Payload.TryGetProperty("previous_attestation_event_hash", out var previous)
                    && hashes.Contains(previous.GetString()!),
                FrozenLedger.SupersedeEventType =>
                    item.Payload.TryGetProperty("previous_attestation_event_hash", out var previous)
                    && hashes.Contains(previous.GetString()!)
                    && DependenciesPresent(
                        item.Payload,
                        "prerequisite_frozen_node_ids",
                        identities),
                "Revoke" => DependenciesPresent(item.Payload, "root_frozen_node_ids", identities),
                _ => true,
            });
            if (index < 0)
            {
                throw new InvalidOperationException(
                    "frozen ledger has no valid linear replay order; remaining="
                    + string.Join(",", remaining.Select(static item =>
                        $"{item.EventType}:{item.Identity}")));
            }

            var item = remaining[index];
            remaining.RemoveAt(index);
            result.Add(item);
            identities.Add(item.Identity);
            if (item.Payload.TryGetProperty("frozen_node_id", out var frozenNodeId)
                && frozenNodeId.ValueKind == JsonValueKind.String)
            {
                identities.Add(frozenNodeId.GetString()!);
            }
            hashes.Add(item.EventHash);
        }

        return result.MoveToImmutable();
    }

    private static bool DependenciesPresent(
        JsonElement payload,
        string property,
        HashSet<string> identities) =>
        payload.TryGetProperty(property, out var dependencies)
        && dependencies.ValueKind == JsonValueKind.Array
        && dependencies.EnumerateArray().All(item =>
            item.ValueKind == JsonValueKind.String && identities.Contains(item.GetString()!));

    internal static TrustedFrozenGitReferences ValidateSuffixReferences(
        IRepositoryGateway repository,
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        string label)
    {
        var references = ScanSuffixReferences(syntax, baseline, label);
        return references.CommitOids.IsEmpty
            && references.TreeOids.IsEmpty
            && references.BlobOids.IsEmpty
            && references.EnvironmentReferences.IsEmpty
                ? TrustedFrozenGitReferences.CreateForTrustedAdapter([], [])
                : repository.ValidateFrozenReferences(references);
    }

    internal static FrozenLedgerReferenceSet ScanSuffixReferences(
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        string label) => FrozenLedger.ScanSuffixReferences(
            syntax,
            baseline.Events.Length,
            baseline.HeadHash) switch
        {
            FrozenLedgerReferenceScanOutcome.Accepted accepted => accepted.References,
            FrozenLedgerReferenceScanOutcome.Rejected rejected => throw new InvalidOperationException(
                label + " fields are invalid: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown ledger reference scan outcome"),
        };

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

    private static FrozenEnvironmentAttestation BuildEnvironment(
        RepositorySnapshot snapshot,
        FrozenLedgerSyntax syntax)
    {
        if (syntax.Lines.Length == 0)
        {
            throw new InvalidOperationException("frozen ledger is missing");
        }

        // The first line is only known to be a JSON object at this point -- DagLedgerLoader
        // checks line shape, not that the ledger opens with a Genesis event. Reading positionally
        // and letting JsonElement throw would hand callers a bare KeyNotFoundException instead of
        // a statement about the ledger.
        if (!syntax.Lines[0].Value.TryGetProperty("payload", out var payload))
        {
            throw new InvalidOperationException(
                "frozen ledger does not open with a Genesis event: first entry carries no payload");
        }

        return BuildEnvironment(
            snapshot,
            RequiredString(payload, "origin_commit_oid"),
            RequiredString(payload, "origin_tree_oid"));
    }

    private static FrozenEnvironmentAttestation BuildEnvironment(
        RepositorySnapshot snapshot,
        string originCommit,
        string originTree)
    {
        if (!snapshot.TryGetFile("lean-toolchain", out var toolchain)
            || !snapshot.TryGetFile("lake-manifest.json", out var manifest))
        {
            throw new InvalidOperationException("pinned Lean environment files are missing");
        }

        var algorithm = originCommit.StartsWith("git-sha256:", StringComparison.Ordinal)
            ? HashAlgorithmName.SHA256
            : HashAlgorithmName.SHA1;
        var lakefiles = new[] { "lakefile.toml", "lakefile.lean" }
            .Where(path => snapshot.TryGetFile(path, out _))
            .ToArray();
        var result = new FrozenEnvironmentAttestation(
            originCommit,
            originTree,
            FrozenContentAddress.ComputeGitBlobOid(toolchain.RawBytes.AsSpan(), algorithm),
            FrozenContentAddress.ComputeGitBlobOid(manifest.RawBytes.AsSpan(), algorithm));
        return lakefiles.Length == 1
            ? result with
            {
                LakefilePath = lakefiles[0],
                LakefileBlobOid = FrozenContentAddress.ComputeGitBlobOid(
                snapshot.Files[RepoPath.CreateKnown(lakefiles[0])].RawBytes.AsSpan(),
                algorithm),
            }
            : result;
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

    private static string RequiredString(JsonElement value, string name) =>
        value.TryGetProperty(name, out var property) && property.ValueKind == JsonValueKind.String
            ? property.GetString() ?? throw new FormatException($"{name} must not be null")
            : throw new FormatException($"{name} must be a string");
}
