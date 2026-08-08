using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record DagLedgerCommandContext(
    string LedgerPath,
    byte[] BaselineBytes,
    FrozenLedgerConsistent Baseline,
    FrozenMaterialCatalog Catalog,
    LeanAxiomReport Report);

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
        var ledgerPath = Path.Combine(
            repositoryRoot,
            FrozenLedgerChangeClassifier.LedgerPath.Replace('/', Path.DirectorySeparatorChar));
        var baselineSyntax = LoadLedgerDirectory(ledgerPath, "existing frozen ledger");
        var baselineBytes = baselineSyntax.RawBytes.ToArray();
        var truth = BuildTruth(repository, leanReportSource);
        var snapshot = truth.Snapshot;
        var report = truth.Report;
        var lean = truth.Lean;
        var dag = truth.Dag;
        var environment = BuildEnvironment(snapshot, baselineSyntax);
        var currentIdentity = Ask(repository.ResolveCurrentRevision);
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
        var catalog = FrozenContentAddress.Build(snapshot, lean, dag, environment, attestations) switch
        {
            FrozenMaterialOutcome.Accepted accepted => accepted.Capability,
            FrozenMaterialOutcome.Rejected rejected => throw new InvalidOperationException(rejected.Message),
            _ => throw new InvalidOperationException("unknown frozen material outcome"),
        };

        var baselineReferences = ScanReferences(baselineSyntax, "existing frozen ledger");
        // Deliberately not wrapped: a refusal here says the ledger records objects this
        // repository does not have -- a verdict about the ledger, not about the environment.
        var trustedBaselineReferences = repository.ValidateFrozenReferences(baselineReferences);
        var baseline = FrozenLedger.ValidateHistoryPrefix(
            baselineSyntax,
            catalog,
            trustedBaselineReferences) switch
        {
            FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
            FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                "existing frozen ledger is invalid: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown ledger validation outcome"),
        };
        return new DagLedgerCommandContext(ledgerPath, baselineBytes, baseline, catalog, report);
    }

    /// Reads the repository, validates the Lean closure and builds the truth DAG -- the part of
    /// Prepare that any DAG consumer needs, without the frozen-ledger work. Callers that only want
    /// the graph (the DAG projection command) share this assembly line rather than growing a
    /// second, drifting copy of it.
    internal static TruthContext BuildTruth(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource)
    {
        var snapshot = Decode(Ask(repository.ReadCurrent));
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

    /// Runs a gateway call that reads repository state, marking anything it throws. A repository
    /// that cannot be read is a fault in the environment, not a statement about the frozen ledger,
    /// and callers classifying failures cannot tell the two apart otherwise -- both arrive as
    /// IOException or InvalidOperationException. Reference validation is not routed through here:
    /// its refusals are about the ledger's contents.
    private static T Ask<T>(Func<T> gatewayCall)
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
        DagLedgerLoader.LoadFiles(Directory.EnumerateFiles(directory, "*.json")
            .Select(path => (path, (ReadOnlyMemory<byte>)File.ReadAllBytes(path)))) switch
        {
            DagLedgerLoadOutcome.Loaded loaded => loaded.Syntax,
            DagLedgerLoadOutcome.Invalid invalid => throw new InvalidOperationException(
                label + " syntax is invalid: " + invalid.Message),
            _ => throw new InvalidOperationException("unknown ledger load outcome"),
        };

    internal static FrozenLedgerReferenceSet ScanReferences(
        FrozenLedgerSyntax syntax,
        string label) =>
        FrozenLedger.ScanReferences(syntax) switch
        {
            FrozenLedgerReferenceScanOutcome.Accepted accepted => accepted.References,
            FrozenLedgerReferenceScanOutcome.Rejected rejected => throw new InvalidOperationException(
                label + " fields are invalid: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown ledger reference scan outcome"),
        };

    private static FrozenEnvironmentAttestation BuildEnvironment(
        RepositorySnapshot snapshot,
        FrozenLedgerSyntax syntax)
    {
        if (syntax.Lines.Length == 0
            || !snapshot.TryGetFile("lean-toolchain", out var toolchain)
            || !snapshot.TryGetFile("lake-manifest.json", out var manifest))
        {
            throw new InvalidOperationException(
                "frozen ledger or pinned Lean environment files are missing");
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

        var originCommit = RequiredString(payload, "origin_commit_oid");
        var originTree = RequiredString(payload, "origin_tree_oid");
        var algorithm = originCommit.StartsWith("git-sha256:", StringComparison.Ordinal)
            ? HashAlgorithmName.SHA256
            : HashAlgorithmName.SHA1;
        return new FrozenEnvironmentAttestation(
            originCommit,
            originTree,
            FrozenContentAddress.ComputeGitBlobOid(toolchain.RawBytes.AsSpan(), algorithm),
            FrozenContentAddress.ComputeGitBlobOid(manifest.RawBytes.AsSpan(), algorithm));
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
