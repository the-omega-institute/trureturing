using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerMathlibReanchorWriter
{
    internal static CommandResult Reanchor(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        try
        {
            var protectedBaseName = ParseArguments(arguments);
            var protectedBase = Decode(DagLedgerCommandPreparation.Ask(
                () => repository.ReadRevision(protectedBaseName)));
            var truth = DagLedgerCommandPreparation.BuildTruth(repository, leanReportSource);
            var currentLedgerFiles = ReadCurrentLedgerFiles(repositoryRoot);
            var protectedLedgerFiles = protectedBase.Files.Values
                .Where(static file =>
                    FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value))
                .ToImmutableArray();
            DagLedgerAppendWriter.RequireUnchangedBaseline(
                LedgerPath(repositoryRoot),
                protectedLedgerFiles,
                "ledger-reanchor-mathlib");

            var baseView = FrozenLedgerBaseViewReader.Read(protectedBase);
            var states = LeanTruthStates.Resolve(truth.Snapshot, truth.Lean);
            var adjacency = LeanImportAdjacency.Build(truth.Snapshot, truth.Lean);
            var selectedPaths = baseView.ActiveByPath.Keys.ToImmutableHashSet();
            var completeCatalog = FrozenContentAddress.Build(
                truth.Snapshot,
                truth.Lean,
                states,
                adjacency) switch
            {
                FrozenMaterialOutcome.Accepted accepted => accepted.Capability,
                FrozenMaterialOutcome.Rejected rejected => throw new InvalidOperationException(
                    "complete frozen catalog build failed: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown frozen material outcome"),
            };
            var driftPaths = baseView.ActiveByPath
                .Where(item => !completeCatalog.ByPath.TryGetValue(item.Key, out var candidate)
                    || candidate.StatementId != item.Value.Material.StatementId)
                .Select(static item => item.Key)
                .OrderBy(static path => path.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            if (driftPaths.IsEmpty)
            {
                return new CommandResult(
                    true,
                    "MATHLIB_REANCHOR replacement_modules=0 recognition=not-required\n",
                    string.Empty);
            }

            var missing = driftPaths
                .Where(path => !completeCatalog.ByPath.ContainsKey(path))
                .ToImmutableArray();
            if (!missing.IsEmpty)
            {
                throw new InvalidOperationException(
                    "canonical Lean report cannot materialize active Closed modules: "
                    + string.Join(", ", missing.Select(static path => path.Value)));
            }

            var newEventFiles = BuildReanchoredEventFiles(
                baseView,
                completeCatalog,
                adjacency,
                driftPaths);
            var replacementFiles = BuildReplacementFiles(
                baseView,
                currentLedgerFiles,
                driftPaths,
                newEventFiles);
            var prospective = ReplaceLedgerSnapshot(truth.Snapshot, replacementFiles);
            var candidateView = FrozenLedgerBaseViewReader.Read(prospective);
            var candidateCatalog = FrozenContentAddress.BuildAdmissionCatalog(
                prospective,
                truth.Lean,
                states,
                adjacency,
                selectedPaths,
                candidateView.ActiveByPath);
            var changes = BuildProspectiveChanges(
                DagLedgerCommandPreparation.Ask(() => repository.ReadChanges(protectedBaseName)),
                baseView,
                newEventFiles,
                driftPaths);
            var deltaEvents = DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
                baseView,
                newEventFiles,
                "generated mathlib reanchor events");
            var recognition = FrozenLedgerIncrementalReplacementRecognition.Recognize(
                baseView,
                prospective,
                changes,
                deltaEvents,
                candidateCatalog) ?? throw new InvalidOperationException(
                    "generated replacement was rejected by FrozenLedgerReplacementRecognition");

            var context = new FrozenLedgerReplacementAuthorizationContext(
                recognition,
                baseView,
                candidateCatalog);
            var pinChanged = EffectiveLeanPins.TryRead(protectedBase, out var basePins)
                && EffectiveLeanPins.TryRead(prospective, out var candidatePins)
                && basePins != candidatePins;
            var propositionFailures = MathlibUpgradePropositionSourceDiagnostics.FindFailures(
                protectedBase,
                prospective,
                recognition.ReanchoredModulePaths,
                baseView,
                candidateCatalog);
            var axiomFailures = recognition.ReanchoredModulePaths
                .Where(path => !candidateCatalog.ByPath.TryGetValue(path, out var material)
                    || material.AxiomClosure.Any(axiom => !LeanAxiomFacts.IsStandard(axiom)))
                .OrderBy(static path => path.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            var authorized = new MathlibUpgradeFrozenLedgerReplacementAuthorization(
                protectedBase,
                prospective).IsAuthorized(context);
            var diagnosedAuthorization = pinChanged
                && propositionFailures.IsEmpty
                && axiomFailures.IsEmpty;
            if (authorized != diagnosedAuthorization)
            {
                throw new InvalidOperationException(
                    "authorization diagnostics disagree with the canonical authorization result");
            }

            DagLedgerAppendWriter.ReplaceEventFiles(
                LedgerPath(repositoryRoot),
                replacementFiles,
                currentLedgerFiles);
            return new CommandResult(
                true,
                RenderResult(
                    driftPaths,
                    pinChanged,
                    propositionFailures,
                    axiomFailures,
                    authorized),
                string.Empty);
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
                DagLedgerAppendWriter.RenderFailure("MATHLIB_REANCHOR_FAILED", exception));
        }
    }

    private static string ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 2
            || arguments[0] != "--base"
            || string.IsNullOrWhiteSpace(arguments[1]))
        {
            throw new InvalidOperationException(
                "USAGE: StrataLint ledger-reanchor-mathlib --base REV");
        }

        return arguments[1];
    }

    private static ImmutableArray<RepositoryFile> BuildReanchoredEventFiles(
        FrozenLedgerBaseView baseView,
        FrozenMaterialCatalog completeCatalog,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency,
        ImmutableArray<RepoPath> driftPaths)
    {
        var driftSet = driftPaths.ToImmutableHashSet();
        var eventHashes = new Dictionary<RepoPath, string>();
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        foreach (var path in LeanImportAdjacency.DependenciesFirst(driftPaths, adjacency)
            .Where(driftSet.Contains))
        {
            var candidate = completeCatalog.ByPath[path];
            var prerequisites = adjacency[path]
                .Select(dependency => eventHashes.TryGetValue(dependency, out var eventHash)
                    ? FrozenNodeId.Create(eventHash)
                    : baseView.ActiveByPath.TryGetValue(dependency, out var active)
                        ? FrozenNodeId.Create(active.EventHash)
                        : throw new InvalidOperationException(
                            $"reanchored module {path.Value} depends on non-active "
                            + dependency.Value))
                .OrderBy(static identity => identity.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            var material = candidate with
            {
                FrozenNodeId = FrozenContentAddress.ComputeFrozenNodeId(
                    path,
                    candidate.StatementId,
                    prerequisites),
                PrerequisiteFrozenNodeIds = prerequisites,
            };
            var file = DagLedgerAppendWriter.BuildNewEventFiles(
                [new FrozenLedgerDraft(
                    "Freeze",
                    FrozenLedgerCanonicalWriter.FreezeElement(
                        FrozenLedgerCanonicalWriter.FreezePayload(material)))])[0];
            var ledgerEvent = DagLedgerLoader.LoadFiles([file]) switch
            {
                DagLedgerFilesLoadOutcome.Loaded loaded => loaded.Events[0],
                DagLedgerFilesLoadOutcome.Invalid invalid => throw new InvalidOperationException(
                    $"generated mathlib reanchor event for {path.Value} is invalid: "
                    + invalid.Message),
                _ => throw new InvalidOperationException("unknown ledger files load outcome"),
            };
            eventHashes.Add(path, ledgerEvent.EventHash);
            files.Add(file);
        }

        return files.ToImmutable();
    }

    private static ImmutableArray<RepositoryFile> BuildReplacementFiles(
        FrozenLedgerBaseView baseView,
        ImmutableArray<RepositoryFile> baselineFiles,
        ImmutableArray<RepoPath> driftPaths,
        ImmutableArray<RepositoryFile> newEventFiles)
    {
        var driftSet = driftPaths.ToImmutableHashSet();
        var replacedEventPaths = baseView.Events
            .Where(item => item.FreezePayload is not null
                && driftSet.Contains(RepoPath.CreateKnown(item.FreezePayload.DescriptorSelector)))
            .Select(static item => item.SourcePath)
            .ToImmutableHashSet();
        return baselineFiles
            .Where(file => !replacedEventPaths.Contains(file.Path))
            .Concat(newEventFiles)
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static RawChangeSet BuildProspectiveChanges(
        RawChangeSet sourceChanges,
        FrozenLedgerBaseView baseView,
        ImmutableArray<RepositoryFile> newEventFiles,
        ImmutableArray<RepoPath> driftPaths)
    {
        var driftSet = driftPaths.ToImmutableHashSet();
        var ledgerChanges = baseView.Events
            .Where(item => item.FreezePayload is not null
                && driftSet.Contains(RepoPath.CreateKnown(item.FreezePayload.DescriptorSelector)))
            .Select(static item => (item.SourcePath.Value, RawChangeKind.Deleted))
            .Concat(newEventFiles.Select(static file =>
                (file.Path.Value, RawChangeKind.Added)));
        return RawChangeSet.CreateWithKinds(sourceChanges.Entries
            .Where(static item =>
                !FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Path.Value))
            .Select(static item => (item.Path.Value, item.Kind))
            .Concat(ledgerChanges));
    }

    private static RepositorySnapshot ReplaceLedgerSnapshot(
        RepositorySnapshot snapshot,
        ImmutableArray<RepositoryFile> replacementFiles) =>
        RepositorySnapshot.Create(snapshot.Files
            .Where(static item =>
                !FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Key.Value))
            .Select(static item => item.Value)
            .Concat(replacementFiles)
            .ToImmutableDictionary(static file => file.Path));

    private static string RenderResult(
        ImmutableArray<RepoPath> driftPaths,
        bool pinChanged,
        ImmutableArray<RepoPath> propositionFailures,
        ImmutableArray<RepoPath> axiomFailures,
        bool authorized)
    {
        var output = "MATHLIB_REANCHOR replacement_modules=" + driftPaths.Length + "\n"
            + "AUTHORIZATION incremental_replacement=pass\n"
            + $"AUTHORIZATION effective_lean_pins_changed={PassFail(pinChanged)}\n"
            + "AUTHORIZATION proposition_source_equivalent="
            + $"{PassFail(propositionFailures.IsEmpty)} failed_modules={propositionFailures.Length}\n"
            + "AUTHORIZATION standard_axiom_closure="
            + $"{PassFail(axiomFailures.IsEmpty)} failed_modules={axiomFailures.Length}\n"
            + $"AUTHORIZATION overall={PassFail(authorized)}\n";
        output += string.Concat(propositionFailures.Select(static path =>
            $"PROPOSITION_SOURCE_FAILURE {path.Value}\n"));
        output += string.Concat(axiomFailures.Select(static path =>
            $"AXIOM_CLOSURE_FAILURE {path.Value}\n"));
        return output;
    }

    private static string PassFail(bool value) => value ? "pass" : "fail";

    private static ImmutableArray<RepositoryFile> ReadCurrentLedgerFiles(string repositoryRoot) =>
        DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(LedgerPath(repositoryRoot));

    private static string LedgerPath(string repositoryRoot) =>
        Path.Combine(
            repositoryRoot,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace(
                '/',
                Path.DirectorySeparatorChar));

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(
                failure.Message),
        };
}
