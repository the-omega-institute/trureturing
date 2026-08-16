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
        RawChangeSet changes,
        Func<FrozenLedgerReferenceSet, TrustedFrozenGitReferences> validateReferences)
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
                TrustedFrozenGitReferences.CreateForTrustedAdapter([], []));
        }

        var deltaFiles = deltaPaths.Select(path => current.TryGetFile(path.Value, out var file)
                ? file
                : throw new FrozenLedgerAdmissionPreparationException(
                    [path],
                    "added frozen-ledger delta path is absent from the candidate snapshot"))
            .ToImmutableArray();
        RejectClosurelessAddedFreezes(deltaFiles);
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

        var inputs = ImmutableArray.CreateBuilder<FrozenLedgerInput>();
        var environmentReferences = ImmutableArray.CreateBuilder<FrozenEnvironmentReference>();
        var requiredAncestorCommitOids = ImmutableArray.CreateBuilder<string>();
        foreach (var item in loaded)
        {
            try
            {
                if (item.EventType == FrozenLedger.SupersedeEventType)
                {
                    var payload = FrozenLedger.ParseSupersede(item.Payload);
                    inputs.Add(payload.Input);
                    environmentReferences.Add(new FrozenEnvironmentReference(
                        payload.Input,
                        payload.Environment));
                }
                else if (item.Input is { } input)
                {
                    inputs.Add(input);
                    if (item.EventType == "Freeze")
                    {
                        requiredAncestorCommitOids.Add(input.BaseCommitOid);
                    }
                }
            }
            catch (Exception exception) when (exception is FormatException
                or InvalidOperationException
                or KeyNotFoundException)
            {
                throw new FrozenLedgerAdmissionPreparationException(
                    [item.SourcePath],
                    "candidate frozen-ledger delta payload is invalid: " + exception.Message);
            }
        }

        var references = FrozenLedgerReferenceSet.Create(
            inputs.ToImmutable(),
            environmentReferences.ToImmutable(),
            [],
            requiredAncestorCommitOids);
        TrustedFrozenGitReferences trusted;
        try
        {
            trusted = inputs.Count == 0 && environmentReferences.Count == 0
                ? TrustedFrozenGitReferences.CreateForTrustedAdapter([], [])
                : validateReferences(references);
        }
        catch (FrozenReferenceRejectionException exception)
        {
            throw new FrozenLedgerAdmissionPreparationException(
                deltaPaths.OrderBy(static path => path.Value, StringComparer.Ordinal).ToImmutableArray(),
                "added frozen-ledger delta recorded an unavailable or inconsistent Git anchor: "
                    + exception.Message);
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
            trusted);
    }

    private static void RejectClosurelessAddedFreezes(
        ImmutableArray<RepositoryFile> deltaFiles)
    {
        foreach (var file in deltaFiles)
        {
            var nodePath = ClosurelessFreezeNodePath(file);
            if (nodePath is null)
            {
                continue;
            }

            throw new FrozenLedgerAdmissionPreparationException(
                [nodePath],
                $"Added Freeze event for {nodePath.Value} must carry axiom_closure. "
                    + $"delta witness: {file.Path.Value}");
        }
    }

    private static RepoPath? ClosurelessFreezeNodePath(RepositoryFile file)
    {
        try
        {
            using var document = JsonDocument.Parse(file.RawBytes.AsSpan().ToArray());
            var root = document.RootElement;
            if (!root.TryGetProperty("event_type", out var eventType)
                || eventType.ValueKind != JsonValueKind.String
                || eventType.GetString() != "Freeze"
                || !root.TryGetProperty("payload", out var payload)
                || payload.ValueKind != JsonValueKind.Object
                || payload.TryGetProperty("axiom_closure", out _)
                || !payload.TryGetProperty("node_path", out var nodePath)
                || nodePath.ValueKind != JsonValueKind.String)
            {
                return null;
            }

            return RepoPath.TryCreate(nodePath.GetString()!, out var parsedPath)
                ? parsedPath
                : null;
        }
        catch (JsonException)
        {
            return null;
        }
    }

    public AdmissionOutcome? Validate(
        FrozenLedgerAdmissionPreparation preparation,
        RepositorySnapshot current,
        AcceptedLeanClosure lean,
        AcyclicTruthDag dag,
        RawChangeSet changes,
        FrozenRevisionIdentity currentIdentity)
    {
        var scope = FrozenLedgerAdmissionScope.Create(changes, preparation, dag);
        FrozenMaterialCatalog catalog;
        try
        {
            AdmissionCatalogBuildCount++;
            catalog = DagLedgerCommandPreparation.BuildAdmissionCatalog(
                current,
                lean,
                dag,
                preparation.BaseView,
                scope,
                currentIdentity);
        }
        catch (Exception exception) when (exception is ArgumentException
            or FormatException
            or InvalidOperationException
            or KeyNotFoundException)
        {
            var affected = scope.Paths.OrderBy(static path => path.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            var witnesses = affected.SelectMany(path => scope.WitnessesFor(path))
                .Distinct()
                .ToImmutableArray();
            return RuleRejection(
                affected.IsEmpty ? witnesses : affected,
                exception.Message + "; delta witness: "
                    + string.Join(", ", witnesses.Select(static path => path.Value)));
        }

        IncrementalValidationCount++;
        var failure = FrozenLedger.ValidateAdmissionDelta(
            preparation,
            scope,
            catalog,
            preparation.TrustedDeltaReferences);
        return failure is null
            ? null
            : RuleRejection(failure.AffectedPaths, failure.Message);
    }

    private ImmutableHashSet<string> ReadProducerPaths()
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
