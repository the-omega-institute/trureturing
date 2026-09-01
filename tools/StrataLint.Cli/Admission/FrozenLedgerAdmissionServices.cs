using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class FrozenLedgerAdmissionPreparationException(
    ImmutableArray<RepoPath> paths,
    string message) : FormatException(message)
{
    internal ImmutableArray<RepoPath> Paths { get; } = paths;
}

internal sealed class MaterializedRepositorySnapshot : IDisposable
{
    private MaterializedRepositorySnapshot(string root) => Root = root;

    internal string Root { get; }

    internal static MaterializedRepositorySnapshot Create(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-snapshot-" + Guid.NewGuid().ToString("N"));
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

            return new MaterializedRepositorySnapshot(root);
        }
        catch
        {
            Directory.Delete(root, recursive: true);
            throw;
        }
    }

    public void Dispose() => Directory.Delete(Root, recursive: true);
}

internal sealed class ProductionFrozenLedgerAdmissionServices : IFrozenLedgerAdmissionServices
{
    private static readonly TimeSpan ProducerPathResolutionTimeout = TimeSpan.FromMinutes(2);
    private readonly string repositoryRoot;
    private readonly Lazy<ImmutableHashSet<string>> producerPaths;

    internal int BaseViewReadCount { get; private set; }

    internal int DeltaEventLoadCount { get; private set; }

    internal int AdmissionCatalogBuildCount { get; private set; }

    internal int IncrementalValidationCount { get; private set; }

    internal ProductionFrozenLedgerAdmissionServices(string repositoryRoot)
    {
        this.repositoryRoot = Path.GetFullPath(repositoryRoot);
        producerPaths = new Lazy<ImmutableHashSet<string>>(ReadProducerPaths);
    }

    internal ProductionFrozenLedgerAdmissionServices(
        string repositoryRoot,
        ImmutableHashSet<string> producerPaths)
    {
        this.repositoryRoot = Path.GetFullPath(repositoryRoot);
        this.producerPaths = new Lazy<ImmutableHashSet<string>>(() => producerPaths);
    }

    public IReadOnlySet<string> LeanReportProducerPaths => producerPaths.Value;

    public FrozenLedgerAdmissionPreparation Prepare(
        RepositorySnapshot current,
        RepositorySnapshot protectedBase,
        RawChangeSet changes)
    {
        BaseViewReadCount++;
        var baseView = FrozenLedgerBaseViewReader.Read(protectedBase);
        var deltaPaths = changes.Entries
            .Where(static change => change.Kind is RawChangeKind.Added or RawChangeKind.Copied
                && FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value))
            .Select(static change => change.Path)
            .ToImmutableHashSet();
        if (deltaPaths.IsEmpty)
        {
            return new FrozenLedgerAdmissionPreparation(
                baseView,
                ImmutableArray<DagLedgerFileEvent>.Empty,
                producerPaths.Value,
                FrozenLedgerReplacementRecognition.Recognize(
                    baseView,
                    current,
                    changes,
                    ImmutableArray<DagLedgerFileEvent>.Empty))
            {
                ProtectedBaseSnapshot = protectedBase,
                CandidateSnapshot = current,
            };
        }

        var deltaFiles = deltaPaths.Select(path => current.TryGetFile(path.Value, out var file)
                ? file
                : throw new FrozenLedgerAdmissionPreparationException(
                    [path],
                    "added frozen-ledger delta path is absent from the candidate snapshot"))
            .ToImmutableArray();
        DeltaEventLoadCount++;
        var loaded = FrozenAcceptedEventLoader.LoadFiles(deltaFiles) switch
        {
            DagLedgerFilesLoadOutcome.Loaded accepted => accepted.Events,
            DagLedgerFilesLoadOutcome.Invalid invalid => throw new FrozenLedgerAdmissionPreparationException(
                deltaPaths.OrderBy(static path => path.Value, StringComparer.Ordinal).ToImmutableArray(),
                "candidate frozen-ledger delta is invalid: " + invalid.Message),
            _ => throw new InvalidOperationException("unknown frozen-ledger delta load outcome"),
        };
        foreach (var item in loaded)
        {
            if (baseView.EventHashes.Contains(item.EventHash)
                || baseView.EventIdentities.Contains(item.Identity))
            {
                throw new FrozenLedgerAdmissionPreparationException(
                    [item.SourcePath],
                    "candidate frozen-ledger delta duplicates a protected-base hash or identity");
            }
        }

        if (!DagLedgerLoader.TryOrderIncrementalDag(
            loaded,
            baseView.EventIdentities,
            baseView.EventHashes,
            out var ordered))
        {
            throw new FrozenLedgerAdmissionPreparationException(
                deltaPaths.OrderBy(static path => path.Value, StringComparer.Ordinal).ToImmutableArray(),
                "candidate frozen-ledger delta does not extend the protected-base dependency DAG");
        }

        return new FrozenLedgerAdmissionPreparation(
            baseView,
            ordered,
            producerPaths.Value,
            FrozenLedgerReplacementRecognition.Recognize(
                baseView,
                current,
                changes,
                ordered))
        {
            ProtectedBaseSnapshot = protectedBase,
            CandidateSnapshot = current,
        };
    }

    public AdmissionOutcome? Validate(
        FrozenLedgerAdmissionPreparation preparation,
        RepositorySnapshot current,
        AcceptedLeanClosure lean,
        LeanAxiomReport report,
        RawChangeSet changes,
        FrozenRevisionIdentity currentIdentity,
        AdmissionCheckTiming timing)
    {
        var scoped = timing.Measure(
            "frozen-ledger-scope",
            () =>
            {
                var states = LeanTruthStates.Resolve(current, lean);
                var adjacency = LeanImportAdjacency.Build(current, lean);
                var scope = FrozenLedgerAdmissionScope.Create(
                    changes,
                    preparation,
                    states,
                    adjacency);
                return (States: states, Adjacency: adjacency, Scope: scope);
            });
        FrozenMaterialCatalog catalog;
        try
        {
            catalog = timing.Measure(
                "frozen-ledger-catalog",
                () =>
                {
                    AdmissionCatalogBuildCount++;
                    var candidateView = FrozenLedgerBaseViewReader.Read(current);
                    return DagLedgerCommandPreparation.BuildAdmissionCatalog(
                        current,
                        lean,
                        scoped.States,
                        scoped.Adjacency,
                        candidateView,
                        scoped.Scope,
                        currentIdentity);
                });
        }
        catch (Exception exception) when (exception is ArgumentException
            or FormatException
            or InvalidOperationException
            or KeyNotFoundException)
        {
            var affected = scoped.Scope.Paths
                .OrderBy(static path => path.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            var witnesses = affected.SelectMany(path => scoped.Scope.WitnessesFor(path))
                .Distinct()
                .ToImmutableArray();
            return RuleRejection(
                affected.IsEmpty ? witnesses : affected,
                exception.Message + "; delta witness: "
                    + string.Join(", ", witnesses.Select(static path => path.Value)));
        }

        var validationPreparation = preparation;
        IFrozenLedgerReplacementAuthorization replacementAuthorization =
            RejectFrozenLedgerReplacementAuthorization.Instance;
        if (preparation.ProtectedBaseSnapshot is { } protectedBaseSnapshot
            && preparation.CandidateSnapshot is { } candidateSnapshot)
        {
            var incrementalRecognition =
                FrozenLedgerIncrementalReplacementRecognition.Recognize(
                    preparation.BaseView,
                    candidateSnapshot,
                    changes,
                    preparation.DeltaEvents,
                    catalog);
            if (incrementalRecognition is not null)
            {
                validationPreparation = preparation with
                {
                    Replacement = incrementalRecognition,
                };
            }

            var mathlibAuthorization =
                new MathlibUpgradeFrozenLedgerReplacementAuthorization(
                    protectedBaseSnapshot,
                    candidateSnapshot);
            replacementAuthorization = new FrozenLedgerReplacementAuthorization(
                mathlibAuthorization);
            if (incrementalRecognition is not null)
            {
                var context = new FrozenLedgerReplacementAuthorizationContext(
                    incrementalRecognition,
                    preparation.BaseView,
                    catalog);
                if (!replacementAuthorization.IsAuthorized(context))
                {
                    return ReplacementAuthorizationRejection(
                        protectedBaseSnapshot,
                        candidateSnapshot,
                        incrementalRecognition,
                        preparation.BaseView,
                        catalog);
                }
            }
        }

        IncrementalValidationCount++;
        var failure = timing.Measure(
            "frozen-ledger-delta",
            () => FrozenLedger.ValidateAdmissionDelta(
                validationPreparation,
                scoped.Scope,
                catalog,
                replacementAuthorization),
            static result => result is not null);
        return failure is null
            ? null
            : RuleRejection(failure.AffectedPaths, failure.Message);
    }

    private ImmutableHashSet<string> ReadProducerPaths() => ReadProducerPaths(repositoryRoot);

    private static AdmissionOutcome.RuleRejected ReplacementAuthorizationRejection(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        FrozenLedgerIncrementalReplacementRecognition recognition,
        FrozenLedgerBaseView baseView,
        FrozenMaterialCatalog catalog)
    {
        var affected = recognition.ReanchoredModulePaths
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        if (!EffectiveLeanPins.TryRead(protectedBase, out var basePins)
            || !EffectiveLeanPins.TryRead(candidate, out var candidatePins)
            || basePins == candidatePins)
        {
            return RuleRejection(
                affected,
                "Mathlib upgrade frozen-ledger replacement authorization failed: "
                    + "effective-lean-pins-changed.");
        }

        var propositionFailures = MathlibUpgradePropositionSourceDiagnostics.FindFailures(
            protectedBase,
            candidate,
            recognition.ReanchoredModulePaths,
            baseView,
            catalog);
        if (!propositionFailures.IsEmpty)
        {
            return RuleRejection(
                propositionFailures,
                "Mathlib upgrade frozen-ledger replacement authorization failed: "
                    + "proposition-source-equivalent.");
        }

        var axiomFailures = affected
            .Where(path => !catalog.ByPath.TryGetValue(path, out var material)
                || material.AxiomClosure.Any(axiom => !LeanAxiomFacts.IsStandard(axiom)))
            .ToImmutableArray();
        return RuleRejection(
            axiomFailures.IsEmpty ? affected : axiomFailures,
            "Mathlib upgrade frozen-ledger replacement authorization failed: "
                + (axiomFailures.IsEmpty
                    ? "canonical authorizer rejected the recognized replacement."
                    : "standard-axiom-closure."));
    }

    private static ImmutableHashSet<string> ReadProducerPaths(string repositoryRoot)
    {
        var script = Path.Combine(
            repositoryRoot,
            "tools",
            "scripts",
            "report",
            "lean-report-input.sh");
        var result = BoundedProcessRunner.Run(
            "bash",
            [script, "producer-paths", "--repository", repositoryRoot],
            repositoryRoot,
            ProducerPathResolutionTimeout,
            16 * 1024 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                "canonical Lean-report producer closure is unavailable: "
                + Encoding.UTF8.GetString(result.StandardError).Trim());
        }

        var paths = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var raw in Encoding.UTF8.GetString(result.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
        {
            if (!RepoPath.TryCreate(raw, out var path) || !paths.Add(path.Value))
            {
                throw new InvalidOperationException(
                    "canonical Lean-report producer closure emitted an invalid or duplicate path");
            }
        }

        return paths.Count > 0
            ? paths.ToImmutable()
            : throw new InvalidOperationException(
                "canonical Lean-report producer closure is empty");
    }

    private static AdmissionOutcome.RuleRejected RuleRejection(
        ImmutableArray<RepoPath> paths,
        string message) => new(paths.Select(path => new Diagnostic(
            RuleId.CreateKnown(8),
            "Frozen Hearts semantics",
            DisplaySeverity.Error,
            AdmissionEffect.Block,
            path.Value,
            message)).ToImmutableArray());
}
