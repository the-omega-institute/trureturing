using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal static class TruthReleaseCommand
{
    private const string SourceRepository = "the-omega-institute/trureturing";
    private const string ProducerRepository = "the-omega-institute/trureturing-producer";

    internal static ExplicitCommandResult Run(
        IRepositoryGateway repository,
        IScribeEmissionVerifier? scribeEmissionVerifier,
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
            var verifier = scribeEmissionVerifier
                ?? throw new InvalidOperationException("truth-release requires Scribe emission verification.");
            TruthExportValidation.RequireGitObjectId(
                options.ProducerPackageCommit,
                "producer_package_commit");
            var identity = DagLedgerCommandPreparation.Ask(repository.ResolveCurrentRevision);
            var snapshot = Decode(DagLedgerCommandPreparation.Ask(
                () => repository.ReadRevision(identity.Revision)));
            var rawLeanReportBytes = ImmutableArray.CreateRange(
                File.ReadAllBytes(options.CandidateLeanReport));
            var preparation = TruthExportCommand.PrepareStrictHistory(
                repository,
                snapshot,
                identity,
                rawLeanReportBytes.AsSpan());
            if (preparation.Outcome is FrozenLedgerValidationOutcome.Rejected rejected)
            {
                return new ExplicitCommandResult(
                    2,
                    string.Empty,
                    $"TRUTH_RELEASE_REJECTED {rejected.Message}\n");
            }

            var frozen = (FrozenLedgerValidationOutcome.Accepted)preparation.Outcome;
            var truth = preparation.Truth;
            var sourceTree = Bare(identity.TreeOid);
            var truthExportBytes = TruthExportJsonWriter.Write(TruthExportProjection.Project(
                frozen.Capability.ActiveFrozenNodes,
                identity.Revision,
                sourceTree));
            var dagMarkdownBytes = CanonicalDagWriter.Write(truth.Dag);
            var truthGraphBytes = AssembleTruthGraph(snapshot, truth, rawLeanReportBytes);
            var blueprintIndexBytes = BlueprintIndexAssembler.Assemble(snapshot);
            var frozenLedgerHeadBytes = FrozenLedgerHeadAssembler.Assemble(preparation.BaseView);
            var residualFrontierBytes = ResidualFrontierAssembler.Assemble(
                snapshot,
                truth.Lean,
                truth.Report,
                verifier);
            var sourceSnapshot = SourceSnapshotAssembler.Assemble(
                snapshot,
                identity,
                SourceRepository,
                options.ProducerPackageCommit,
                truthGraphBytes,
                rawLeanReportBytes,
                dagMarkdownBytes,
                residualFrontierBytes,
                truthExportBytes,
                frozenLedgerHeadBytes,
                preparation.BaseView.EventCount);
            var source = new TruthReleaseSource(SourceRepository, identity.Revision, sourceTree);
            var digest = TruthReleaseBundleWriter.WriteBundle(
                options.OutDirectory,
                new TruthReleaseBundleInput(
                    sourceSnapshot,
                    truthGraphBytes,
                    rawLeanReportBytes,
                    truthExportBytes,
                    blueprintIndexBytes,
                    frozenLedgerHeadBytes,
                    residualFrontierBytes,
                    source,
                    Trust(),
                    new TruthReleaseProducer(
                        ProducerRepository,
                        options.ProducerPackageCommit,
                        ReadOnly: true),
                    options.ProducedAt));
            return new ExplicitCommandResult(
                0,
                $"TRUTH_RELEASE release_digest={digest} source_commit={identity.Revision} "
                    + $"out={Path.GetFullPath(options.OutDirectory)}\n",
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
                $"TRUTH_RELEASE_INVALID {exception.Message}\n");
        }
    }

    private static ImmutableArray<byte> AssembleTruthGraph(
        RepositorySnapshot snapshot,
        TruthContext truth,
        ImmutableArray<byte> rawLeanReportBytes)
    {
        using var materialized = MaterializedSnapshot.Create(snapshot);
        var catalog = DeclarationCatalog.Create(truth.Report);
        var sourcePaths = snapshot.Files.Keys
            .Where(static path => path.Value.StartsWith("Blueprint/", StringComparison.Ordinal)
                && path.Value.EndsWith(".scribe.cs", StringComparison.Ordinal))
            .Select(static path => path.Value)
            .ToArray();
        var definitions = DocumentDefinitions
            .Discover(typeof(DocumentDefinitions).Assembly, materialized.Root)
            .Where(definition => sourcePaths.Contains(
                ScribeEmissionAttestation.DefinitionPath(definition.Document.Header.Gid.Value),
                StringComparer.Ordinal))
            .ToArray();
        var sourceFindings = DocumentDefinitions.CheckRepositorySourceBijection(sourcePaths, definitions);
        if (sourceFindings.Length > 0)
        {
            throw new InvalidOperationException(sourceFindings[0]);
        }

        var documents = definitions
            .Select(definition => definition.Document.ResolveDeclarations(catalog))
            .ToArray();
        var census = ReceiptFreeDocumentCatalog.Load(
            materialized.Root,
            documents,
            tolerateAbsentDocuments: true);
        var graph = DocumentGraphAssembler.Assemble(
            documents,
            catalog,
            census.ReceiptFreeDocumentGids);
        var projection = DocumentGraphProjectionBuilder.Create(
            definitions.Select(definition => new DocumentGraphDocument(
                definition.RelativePath.Value,
                definition.Document,
                census.ReceiptFreeDocumentGids.Contains(definition.Document.Header.Gid.Value)
                    ? "receipt-free"
                    : "receipt-bound")),
            graph,
            catalog,
            truth.Dag.Nodes
                .Select(static node => node.RepoPath.Value)
                .ToHashSet(StringComparer.Ordinal));
        var provenance = new TruthGraphProvenance(
            SnapshotContentDigest.Compute(snapshot),
            RawLeanReportArtifact.ContentAddress(rawLeanReportBytes.AsSpan()));
        return TruthGraphJsonWriter.Write(
            TruthGraphModelBuilder.Create(truth.Dag, provenance, projection));
    }

    private static TruthReleaseTrust Trust() => new(
        CommitOnProtectedDev: true,
        ImmutableArray.Create(
            new TruthReleaseRequiredCheck(
                "Candidate harness engineering checks",
                "success"),
            new TruthReleaseRequiredCheck(
                "Canonical Lean report production",
                "success"),
            new TruthReleaseRequiredCheck(
                "Content-addressed dev baseline admission",
                "success")),
        BlessedBy: null);

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(
                "immutable revision snapshot is invalid: " + failure.Message),
        };

    private static string Bare(string taggedOid)
    {
        var separator = taggedOid.IndexOf(':', StringComparison.Ordinal);
        return separator < 0 ? taggedOid : taggedOid[(separator + 1)..];
    }

    private static bool TryParseArguments(
        IReadOnlyList<string> arguments,
        out TruthReleaseArguments options)
    {
        options = default;
        if (arguments.Count != 8)
        {
            return false;
        }

        string? outDirectory = null;
        string? candidateLeanReport = null;
        string? producerPackageCommit = null;
        string? producedAt = null;
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
                case "--producer-package-commit" when producerPackageCommit is null:
                    producerPackageCommit = value;
                    break;
                case "--produced-at" when producedAt is null:
                    producedAt = value;
                    break;
                default:
                    return false;
            }
        }

        if (outDirectory is null
            || candidateLeanReport is null
            || producerPackageCommit is null
            || producedAt is null)
        {
            return false;
        }

        options = new TruthReleaseArguments(
            outDirectory,
            candidateLeanReport,
            producerPackageCommit,
            producedAt);
        return true;
    }

    private static ExplicitCommandResult Usage() => new(
        1,
        string.Empty,
        "USAGE: StrataLint truth-release --out DIR --candidate-lean-report FILE "
            + "--producer-package-commit COMMIT --produced-at TIMESTAMP\n");

    private readonly record struct TruthReleaseArguments(
        string OutDirectory,
        string CandidateLeanReport,
        string ProducerPackageCommit,
        string ProducedAt);

    private sealed class MaterializedSnapshot : IDisposable
    {
        private MaterializedSnapshot(string root) => Root = root;

        internal string Root { get; }

        internal static MaterializedSnapshot Create(RepositorySnapshot snapshot)
        {
            var root = Path.Combine(
                Path.GetTempPath(),
                "stratalint-truth-release-" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(root);
            try
            {
                foreach (var (path, file) in snapshot.Files
                    .OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
                {
                    var destination = Path.Combine(
                        root,
                        path.Value.Replace('/', Path.DirectorySeparatorChar));
                    Directory.CreateDirectory(Path.GetDirectoryName(destination)
                        ?? throw new InvalidOperationException("snapshot path has no parent directory"));
                    File.WriteAllBytes(destination, file.RawBytes.AsSpan());
                }

                return new MaterializedSnapshot(root);
            }
            catch
            {
                Directory.Delete(root, recursive: true);
                throw;
            }
        }

        public void Dispose() => Directory.Delete(Root, recursive: true);
    }
}
