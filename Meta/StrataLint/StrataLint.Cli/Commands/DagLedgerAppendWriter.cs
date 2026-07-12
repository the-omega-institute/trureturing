using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerAppendWriter
{
    internal static CommandResult Append(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 2 || arguments[0] != "--candidate-lean-report")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-append --candidate-lean-report FILE");
            }

            var ledgerPath = Path.Combine(
                repositoryRoot,
                FrozenLedgerChangeClassifier.LedgerPath.Replace('/', Path.DirectorySeparatorChar));
            var baselineBytes = File.ReadAllBytes(ledgerPath);
            var baselineSyntax = LoadLedger(baselineBytes, "existing frozen ledger");
            var snapshot = Decode(repository.ReadCurrent());
            var lean = ValidateLean(
                snapshot,
                RawLeanReportArtifact.ReadFile(arguments[1], snapshot));
            var dag = AcyclicTruthDag.Build(snapshot, lean) switch
            {
                DagBuildOutcome.Accepted accepted => accepted.Capability,
                DagBuildOutcome.Rejected rejected => throw new InvalidOperationException(
                    "candidate truth DAG is cyclic: "
                    + string.Join(" -> ", rejected.Witness.Select(static path => path.Value))),
                _ => throw new InvalidOperationException("unknown truth DAG outcome"),
            };
            var environment = BuildEnvironment(snapshot, baselineSyntax);
            var currentIdentity = repository.ResolveCurrentRevision();
            if (currentIdentity.CommitOid.StartsWith("git-sha256:", StringComparison.Ordinal)
                != environment.OriginCommitOid.StartsWith("git-sha256:", StringComparison.Ordinal))
            {
                throw new InvalidOperationException("current revision and frozen Genesis use different Git hash algorithms");
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
            var candidateBytes = FrozenLedgerGenerator.AppendMissingFreezes(baseline, catalog);
            if (candidateBytes.AsSpan().SequenceEqual(baselineBytes))
            {
                return new CommandResult(
                    true,
                    $"LEDGER_APPEND no missing freezes events={baseline.Events.Length} head={baseline.HeadHash}\n",
                    string.Empty);
            }

            var candidateSyntax = LoadLedger(candidateBytes.AsSpan(), "generated frozen ledger");
            var candidateReferences = ScanReferences(candidateSyntax, "generated frozen ledger");
            var trustedCandidateReferences = repository.ValidateFrozenReferences(candidateReferences);
            var candidate = FrozenLedger.ValidateCandidate(
                candidateSyntax,
                baseline,
                catalog,
                trustedCandidateReferences) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "generated frozen ledger is invalid: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };
            if (!File.ReadAllBytes(ledgerPath).AsSpan().SequenceEqual(baselineBytes))
            {
                throw new InvalidOperationException("events.jsonl changed while ledger-append was validating it");
            }

            File.WriteAllBytes(ledgerPath, candidateBytes.AsSpan());
            var appended = candidate.Events
                .Skip(baseline.Events.Length)
                .OfType<FrozenLedgerEvent.Freeze>()
                .ToImmutableArray();
            var output = $"LEDGER_APPEND appended_freezes={appended.Length} "
                + $"events={candidate.Events.Length} head={candidate.HeadHash}\n"
                + string.Concat(appended.Select(static item => $"FROZEN {item.Payload.NodePath.Value}\n"));
            return new CommandResult(true, output, string.Empty);
        }
        catch (Exception exception) when (
            exception is ArgumentException
                or FormatException
                or IOException
                or InvalidOperationException
                or JsonException
                or KeyNotFoundException
                or UnauthorizedAccessException)
        {
            return new CommandResult(
                false,
                string.Empty,
                "LEDGER_APPEND_FAILED " + exception.Message + "\n");
        }
    }

    private static FrozenEnvironmentAttestation BuildEnvironment(
        RepositorySnapshot snapshot,
        FrozenLedgerSyntax syntax)
    {
        if (syntax.Lines.Length == 0
            || !snapshot.TryGetFile("lean-toolchain", out var toolchain)
            || !snapshot.TryGetFile("lake-manifest.json", out var manifest))
        {
            throw new InvalidOperationException("frozen ledger or pinned Lean environment files are missing");
        }

        var payload = syntax.Lines[0].Value.GetProperty("payload");
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

    private static FrozenLedgerSyntax LoadLedger(ReadOnlySpan<byte> bytes, string label) =>
        DagLedgerLoader.Load(bytes) switch
        {
            DagLedgerLoadOutcome.Loaded loaded => loaded.Syntax,
            DagLedgerLoadOutcome.Invalid invalid => throw new InvalidOperationException(
                label + " syntax is invalid: " + invalid.Message),
            _ => throw new InvalidOperationException("unknown ledger load outcome"),
        };

    private static FrozenLedgerReferenceSet ScanReferences(FrozenLedgerSyntax syntax, string label) =>
        FrozenLedger.ScanReferences(syntax) switch
        {
            FrozenLedgerReferenceScanOutcome.Accepted accepted => accepted.References,
            FrozenLedgerReferenceScanOutcome.Rejected rejected => throw new InvalidOperationException(
                label + " fields are invalid: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown ledger reference scan outcome"),
        };

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

    private static string RequiredString(JsonElement value, string name) =>
        value.TryGetProperty(name, out var property) && property.ValueKind == JsonValueKind.String
            ? property.GetString() ?? throw new FormatException($"{name} must not be null")
            : throw new FormatException($"{name} must be a string");
}
