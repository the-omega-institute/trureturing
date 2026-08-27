using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerSupersedeWriter
{
    internal static CommandResult Supersede(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 2 || arguments[0] != "--candidate-lean-report")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-supersede --candidate-lean-report FILE");
            }

            var candidate = DagLedgerCommandPreparation.PrepareCandidate(
                repositoryRoot,
                repository,
                new FileLeanReportSource(arguments[1]));
            var baselineFiles = candidate.BaselineFiles;
            var protectedBase = candidate.BaseView;
            var pins = FrozenLedger.EnvironmentPins(candidate.Catalog.Environment);
            var protectedSnapshots = new ProtectedPinSnapshotReader(repository);

            var generated = BuildEvents(
                protectedBase,
                candidate.Catalog,
                candidate.Report,
                candidate.Changes,
                candidate.Snapshot,
                pins,
                protectedSnapshots.Read);
            if (generated.IsEmpty)
            {
                return new CommandResult(
                    true,
                    $"LEDGER_SUPERSEDE no changed environment pins events={protectedBase.EventCount}\n",
                    string.Empty);
            }

            var references = FrozenLedgerReferenceSet.Create(
                generated.Select(static item => item.Payload.Input).ToImmutableArray(),
                generated.Select(static item => new FrozenEnvironmentReference(
                    item.Payload.Input,
                    item.Payload.Environment)).ToImmutableArray(),
                []);
            var trustedCandidateReferences = repository.ValidateFrozenReferences(references);
            ValidateGeneratedEvents(
                protectedBase,
                candidate.Catalog,
                candidate.Report,
                candidate.Changes,
                candidate.Snapshot,
                trustedCandidateReferences,
                generated,
                protectedSnapshots.Read);

            var eventFiles = generated.Select(static item => item.File).ToImmutableArray();
            _ = DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
                protectedBase,
                eventFiles,
                "generated frozen ledger suffix");

            DagLedgerAppendWriter.WriteEventFiles(
                candidate.LedgerPath,
                eventFiles,
                candidate.BaselineFiles);
            var output = $"LEDGER_SUPERSEDE appended_supersedes={generated.Length} "
                + $"events={protectedBase.EventCount + generated.Length}\n"
                + string.Concat(generated.Select(item =>
                    $"SUPERSEDED {protectedBase.ActiveByCase[item.Payload.CaseId].Material.RepoPath.Value}\n"));
            return new CommandResult(true, output, string.Empty);
        }
        catch (Exception exception) when (
            exception is ArgumentException
                or FormatException
                or IOException
                or InvalidOperationException
                or JsonException
                or KeyNotFoundException
                or UnauthorizedAccessException
                or DagLedgerCommandPreparation.LeanReportUnusableException
                or DagLedgerCommandPreparation.RepositoryUnavailableException)
        {
            return new CommandResult(
                false,
                string.Empty,
                DagLedgerAppendWriter.RenderFailure("LEDGER_SUPERSEDE_FAILED", exception));
        }
    }

    private static ImmutableArray<GeneratedSupersede> BuildEvents(
        FrozenLedgerBaseView protectedBase,
        FrozenMaterialCatalog candidateCatalog,
        LeanAxiomReport report,
        RawChangeSet changes,
        RepositorySnapshot snapshot,
        FrozenEnvironmentPins pins,
        Func<FrozenActiveEntry, RepositorySnapshot> protectedSnapshot)
    {
        var result = ImmutableArray.CreateBuilder<GeneratedSupersede>();
        foreach (var entry in protectedBase.ActiveByCase.Values.OrderBy(
            static item => item.Material.RepoPath.Value,
            StringComparer.Ordinal))
        {
            if (!FrozenLedger.EnvironmentPinsChanged(pins, entry))
            {
                continue;
            }

            if (!candidateCatalog.ByPath.TryGetValue(entry.Material.RepoPath, out var material))
            {
                throw new InvalidOperationException(
                    $"Active module {entry.Material.RepoPath.Value} is not Closed in the candidate report.");
            }

            var input = FrozenLedgerCanonicalWriter.FreezePayload(
                candidateCatalog.Environment,
                material).Input with
            {
                SupportingBlobOids = ImmutableArray<string>.Empty,
            };
            var payload = new FrozenSupersedePayload(
                material.AxiomClosure,
                entry.Payload.CaseId,
                material.DeclarationStatementIds,
                pins,
                material.FrozenNodeId,
                input,
                material.PrerequisiteFrozenNodeIds,
                entry.LastAttestationEventHash,
                material.StatementId,
                material.WitnessId);
            FrozenLedger.ValidateSupersedeStrength(
                payload,
                entry,
                !LeanImportClosure.RepositoryPaths(
                    report,
                    entry.Material.RepoPath).Overlaps(changes.Paths),
                LeanImportClosure.ExternalImportsHaveNamedPinCoverage(
                    report,
                    entry.Material.RepoPath,
                    snapshot),
                material.StatementId == entry.Material.StatementId
                    || LeanImportClosure.RelevantSemanticPinsChanged(
                        report,
                        entry.Material.RepoPath,
                        protectedSnapshot(entry),
                        snapshot),
                LeanImportClosure.CandidateStatementsAvoidTrivialTruth(
                    report,
                    entry.Material.RepoPath));
            var element = FrozenLedgerCanonicalWriter.SupersedeElement(payload);
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                FrozenLedger.SupersedeEventType,
                element);
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(
                FrozenLedger.SupersedeEventType,
                element,
                encoded.Hash);
            result.Add(new GeneratedSupersede(
                payload,
                encoded.Hash,
                element,
                new RepositoryFile(
                    RepoPath.CreateKnown(FrozenLedgerChangeClassifier.AcceptedPath(identity)),
                    encoded.Bytes,
                    Encoding.UTF8.GetString(encoded.Bytes.AsSpan()))));
        }

        return result.ToImmutable();
    }

    private static void ValidateGeneratedEvents(
        FrozenLedgerBaseView protectedBase,
        FrozenMaterialCatalog candidateCatalog,
        LeanAxiomReport report,
        RawChangeSet changes,
        RepositorySnapshot snapshot,
        TrustedFrozenGitReferences trustedReferences,
        ImmutableArray<GeneratedSupersede> generated,
        Func<FrozenActiveEntry, RepositorySnapshot> protectedSnapshot)
    {
        var active = protectedBase.ActiveByCase.ToDictionary(
            static item => item.Key,
            static item => item.Value,
            StringComparer.Ordinal);
        foreach (var item in generated)
        {
            var payload = FrozenLedger.ValidateSupersede(
                item.Element,
                active,
                trustedReferences,
                candidateCatalog,
                !LeanImportClosure.RepositoryPaths(
                    report,
                    active[item.Payload.CaseId].Material.RepoPath).Overlaps(changes.Paths),
                    LeanImportClosure.ExternalImportsHaveNamedPinCoverage(
                        report,
                        active[item.Payload.CaseId].Material.RepoPath,
                        snapshot),
                    item.Payload.StatementId == active[item.Payload.CaseId].Material.StatementId
                        || LeanImportClosure.RelevantSemanticPinsChanged(
                            report,
                            active[item.Payload.CaseId].Material.RepoPath,
                            protectedSnapshot(active[item.Payload.CaseId]),
                            snapshot),
                    LeanImportClosure.CandidateStatementsAvoidTrivialTruth(
                        report,
                        active[item.Payload.CaseId].Material.RepoPath));
            active[payload.CaseId] = FrozenLedger.ApplySupersede(
                active[payload.CaseId],
                payload,
                item.EventHash,
                candidateCatalog.ByPath[active[payload.CaseId].Material.RepoPath]);
        }
    }

    private sealed record GeneratedSupersede(
        FrozenSupersedePayload Payload,
        string EventHash,
        JsonElement Element,
        RepositoryFile File);

    private sealed class FileLeanReportSource(string path) : ILeanReportSource
    {
        public LeanAxiomReport Load(RepositorySnapshot snapshot) =>
            RawLeanReportArtifact.ReadFile(path, snapshot);
    }
}

internal sealed class ProtectedPinSnapshotReader(IRepositoryGateway repository)
{
    private readonly Dictionary<string, RepositorySnapshot> snapshots = new(StringComparer.Ordinal);

    internal RepositorySnapshot Read(FrozenActiveEntry entry)
    {
        ArgumentNullException.ThrowIfNull(entry);
        var supporting = entry.Payload.Input.SupportingBlobOids;
        if (supporting.Length != 2
            || supporting.Distinct(StringComparer.Ordinal).Count() != 2)
        {
            throw new InvalidOperationException(
                "protected semantic pins require exactly two distinct supporting blob OIDs");
        }

        var key = string.Join('\n', supporting.Order(StringComparer.Ordinal));
        if (!snapshots.TryGetValue(key, out var snapshot))
        {
            snapshot = Decode(DagLedgerCommandPreparation.Ask(
                () => repository.ReadEnvironmentPinBlobs(entry.Payload.Input)));
            snapshots.Add(key, snapshot);
        }

        return snapshot;
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(
                "protected semantic-pin snapshot is unavailable: " + failure.Message),
        };
}
