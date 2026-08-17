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
            var generated = BuildEvents(protectedBase, candidate.Catalog, pins);
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
                trustedCandidateReferences,
                generated);

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
        FrozenEnvironmentPins pins)
    {
        var result = ImmutableArray.CreateBuilder<GeneratedSupersede>();
        foreach (var entry in protectedBase.ActiveByCase.Values.OrderBy(
            static item => item.Material.RepoPath.Value,
            StringComparer.Ordinal))
        {
            if (entry.Environment == pins)
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
            FrozenLedger.ValidateSupersedeStrength(payload, entry);
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
        TrustedFrozenGitReferences trustedReferences,
        ImmutableArray<GeneratedSupersede> generated)
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
                candidateCatalog);
            FrozenLedger.ValidateSupersedeStrength(
                payload,
                protectedBase.ActiveByCase[payload.CaseId]);
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
