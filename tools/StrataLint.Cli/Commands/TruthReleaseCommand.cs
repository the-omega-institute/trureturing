using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal static class TruthReleaseCommand
{
    private const string SourceRepository = "the-omega-institute/trureturing";
    private const string ProducerRepository = "the-omega-institute/trureturing";

    internal static ExplicitCommandResult Run(IRepositoryGateway repository,
        IScribeEmissionVerifier? scribeEmissionVerifier, IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        if (!TryParseArguments(arguments, out var options, out var missingScribePack))
            return missingScribePack ? MissingScribePackUsage() : Usage();

        try
        {
            var suppliedDefinitions = ScribePackInput.ReadDefinitions(
                options.ScribePackPath, options.ScribePackDigest);
            var verifier = scribeEmissionVerifier
                ?? throw new InvalidOperationException("truth-release requires Scribe emission verification.");
            TruthExportValidation.RequireGitObjectId(
                options.ProducerPackageCommit,
                "producer_package_commit");
            var identity = DagLedgerCommandPreparation.Ask(repository.ResolveCurrentRevision);
            var contentHashes = new Dictionary<string, ReadOnlyMemory<byte>>(StringComparer.Ordinal);
            var snapshot = Decode(DagLedgerCommandPreparation.Ask(
                () => repository.ReadRevisionProjection(identity.Revision, IsReleaseInput,
                    (path, hash) => contentHashes.Add(path, hash))));
            var report = RawLeanReportArtifact.ReadFile(
                options.CandidateLeanReport, snapshot, out var rawLeanReportBytes, validateMaterials: false);
            if (!TruthExportCommand.TryPrepareFrozenTruth(snapshot, report, out var prepared, out var rejection))
                return new(2, string.Empty, $"TRUTH_RELEASE_REJECTED {rejection}\n");

            var truth = prepared.Truth;
            verifier.Verify(snapshot, truth.Report, suppliedDefinitions);
            var sourceTree = Bare(identity.TreeOid);
            var truthExportBytes = TruthExportJsonWriter.Write(TruthExportProjection.Project(
                prepared.Catalog.ClosedNodes,
                prepared.Frozen.Selectors.ToImmutableHashSet(),
                identity.Revision,
                sourceTree));
            var projection = TruthDagProjectionAssembler.Build(truth.Snapshot, truth.Lean, prepared.States);
            var dagMarkdownBytes = CanonicalDagWriter.Write(projection);
            var truthGraphBytes = AssembleTruthGraph(
                contentHashes, truth, projection, rawLeanReportBytes, suppliedDefinitions);
            var blueprintIndexBytes = BlueprintIndexAssembler.Assemble(snapshot);
            var sourceSnapshot = SourceSnapshotAssembler.Assemble(
                snapshot,
                identity,
                SourceRepository,
                options.ProducerPackageCommit,
                truthGraphBytes,
                rawLeanReportBytes,
                dagMarkdownBytes,
                truthExportBytes);
            var digest = TruthReleaseBundleWriter.WriteBundle(
                options.OutDirectory,
                new TruthReleaseBundleInput(
                    sourceSnapshot,
                    truthGraphBytes,
                    rawLeanReportBytes,
                    truthExportBytes,
                    blueprintIndexBytes,
                    new TruthReleaseSource(SourceRepository, identity.Revision, sourceTree),
                    options.Trust,
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
        IReadOnlyDictionary<string, ReadOnlyMemory<byte>> contentHashes,
        TruthContext truth,
        TruthDagProjection projection,
        ImmutableArray<byte> rawLeanReportBytes,
        IReadOnlyList<DocumentDefinition> suppliedDefinitions)
    {
        var provenance = new TruthGraphProvenance(
            SnapshotContentDigest.ComputeContentHashes(
                contentHashes,
                suppliedDefinitions.Select(static definition => definition.RelativePath.Value)),
            RawLeanReportArtifact.ContentAddress(rawLeanReportBytes.AsSpan()));
        return TruthGraphJsonWriter.Write(
            TruthGraphModelBuilder.Create(
                projection,
                provenance,
                suppliedDefinitions,
                string.Empty,
                DeclarationCatalog.Create(truth.Report),
                tolerateAbsentDocuments: true));
    }

    internal static bool IsReleaseInput(string path) =>
        !path.StartsWith("Meta/Digestion/", StringComparison.Ordinal)
        && !path.StartsWith("docs/", StringComparison.Ordinal);

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
        out TruthReleaseArguments options,
        out bool missingScribePack)
    {
        options = default;
        missingScribePack = false;
        if (arguments.Count % 2 != 0)
        {
            return false;
        }

        string? outDirectory = null;
        string? candidateLeanReport = null;
        string? producerPackageCommit = null;
        string? producedAt = null;
        string? scribePackPath = null;
        string? scribePackDigest = null;
        bool? commitOnProtectedDev = null;
        var requiredChecks = ImmutableArray.CreateBuilder<TruthReleaseRequiredCheck>();
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
                case "--scribe-pack" when scribePackPath is null:
                    scribePackPath = value;
                    break;
                case "--scribe-pack-digest" when scribePackDigest is null:
                    scribePackDigest = value;
                    break;
                case "--commit-on-protected-dev" when commitOnProtectedDev is null
                    && bool.TryParse(value, out var parsedCommitOnProtectedDev):
                    commitOnProtectedDev = parsedCommitOnProtectedDev;
                    break;
                case "--required-check" when TryParseRequiredCheck(value, out var requiredCheck):
                    requiredChecks.Add(requiredCheck);
                    break;
                default:
                    return false;
            }
        }

        if (outDirectory is null
            || candidateLeanReport is null
            || producerPackageCommit is null
            || producedAt is null
            || commitOnProtectedDev is null
            || requiredChecks.Count == 0)
        {
            return false;
        }

        if (scribePackPath is null || scribePackDigest is null)
        {
            missingScribePack = true;
            return false;
        }

        if (!ScribePackInput.IsDigest(scribePackDigest))
        {
            return false;
        }

        options = new TruthReleaseArguments(
            outDirectory,
            candidateLeanReport,
            producerPackageCommit,
            producedAt,
            new TruthReleaseTrust(
                commitOnProtectedDev.Value,
                requiredChecks.ToImmutable(),
                BlessedBy: null),
            scribePackPath,
            scribePackDigest);
        return true;
    }

    private static bool TryParseRequiredCheck(
        string value,
        out TruthReleaseRequiredCheck requiredCheck)
    {
        requiredCheck = null!;
        var separator = value.IndexOf('=', StringComparison.Ordinal);
        if (separator <= 0 || separator == value.Length - 1)
        {
            return false;
        }

        requiredCheck = new TruthReleaseRequiredCheck(
            value[..separator],
            value[(separator + 1)..]);
        return true;
    }

    private static ExplicitCommandResult Usage() => new(
        1,
        string.Empty,
        "USAGE: StrataLint truth-release --out DIR --candidate-lean-report FILE "
            + "--producer-package-commit COMMIT --produced-at TIMESTAMP "
            + "--commit-on-protected-dev true|false "
            + "--required-check NAME=CONCLUSION (required: "
            + "every required check supplied by the caller" + ") "
            + "--scribe-pack FILE --scribe-pack-digest HEX64\n");

    private static ExplicitCommandResult MissingScribePackUsage() => new(
        2,
        string.Empty,
        "TRUTH_RELEASE_INVALID required Scribe resource pack: "
            + "--scribe-pack FILE --scribe-pack-digest HEX64\n");

    private readonly record struct TruthReleaseArguments(
        string OutDirectory,
        string CandidateLeanReport,
        string ProducerPackageCommit,
        string ProducedAt,
        TruthReleaseTrust Trust,
        string ScribePackPath,
        string ScribePackDigest);
}
