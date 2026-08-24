using System.Collections.Immutable;

namespace StrataLint.Engine;

public enum ArtifactClass
{
    F,
    B,
    E,
    C,
    L,
    P,
    Meta,
    GitHub,
    Agents,
    Docs,
    Root,
    Other,
}

public enum CoverageLedgerState
{
    Frozen,
    Open,
    Tail,
    Semantic,
}

internal static class CoverageNames
{
    internal static ImmutableArray<string> ArtifactClasses { get; } =
    [
        "F", "B", "E", "C", "L", "P", "Meta", ".github", "agents", "docs", "root", "other",
    ];

    internal static string Class(ArtifactClass value) => value switch
    {
        ArtifactClass.F => "F",
        ArtifactClass.B => "B",
        ArtifactClass.E => "E",
        ArtifactClass.C => "C",
        ArtifactClass.L => "L",
        ArtifactClass.P => "P",
        ArtifactClass.Meta => "Meta",
        ArtifactClass.GitHub => ".github",
        ArtifactClass.Agents => "agents",
        ArtifactClass.Docs => "docs",
        ArtifactClass.Root => "root",
        ArtifactClass.Other => "other",
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };

    internal static string Ledger(CoverageLedgerState value) => value switch
    {
        CoverageLedgerState.Frozen => "frozen",
        CoverageLedgerState.Open => "open",
        CoverageLedgerState.Tail => "tail",
        CoverageLedgerState.Semantic => "semantic",
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
}

public sealed class CoverageLedgerIndex
{
    private readonly ImmutableDictionary<RepoPath, CoverageLedgerState> states;

    private CoverageLedgerIndex(ImmutableDictionary<RepoPath, CoverageLedgerState> states) =>
        this.states = states;

    public static CoverageLedgerIndex Empty { get; } = new(
        ImmutableDictionary<RepoPath, CoverageLedgerState>.Empty);

    public static CoverageLedgerIndex Create(
        params (string Path, CoverageLedgerState State)[] entries)
    {
        var builder = ImmutableDictionary.CreateBuilder<RepoPath, CoverageLedgerState>();
        foreach (var entry in entries)
        {
            if (!RepoPath.TryCreate(entry.Path, out var path) || !builder.TryAdd(path, entry.State))
            {
                throw new ArgumentException($"invalid or duplicate coverage ledger path: {entry.Path}");
            }
        }

        return new CoverageLedgerIndex(builder.ToImmutable());
    }

    public static CoverageLedgerIndex FromDag(
        AcyclicTruthDag dag,
        IEnumerable<RepoPath> frozenPaths,
        RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(dag);
        ArgumentNullException.ThrowIfNull(frozenPaths);
        ArgumentNullException.ThrowIfNull(snapshot);
        var frozen = frozenPaths.ToHashSet();
        var dagPaths = dag.Nodes.Select(static node => node.RepoPath).ToHashSet();
        var absent = frozen.Where(path => !dagPaths.Contains(path))
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToArray();
        if (absent.Length > 0)
        {
            throw new InvalidOperationException(
                "frozen ledger paths are absent from TruthDAG: "
                + string.Join(", ", absent.Select(static path => path.Value)));
        }

        var builder = ImmutableDictionary.CreateBuilder<RepoPath, CoverageLedgerState>();
        foreach (var node in dag.Nodes)
        {
            if (frozen.Contains(node.RepoPath))
            {
                if (node.State is not TruthState.Closed)
                {
                    throw new InvalidOperationException(
                        $"frozen ledger path is not Closed in TruthDAG: {node.RepoPath.Value}");
                }

                builder.Add(node.RepoPath, CoverageLedgerState.Frozen);
                continue;
            }

            var state = node.State switch
            {
                TruthState.Open => CoverageLedgerState.Open,
                TruthState.Tail => CoverageLedgerState.Tail,
                _ => (CoverageLedgerState?)null,
            };
            if (state is not null) builder.Add(node.RepoPath, state.Value);
        }

        // GID-addressed artifacts outside the managed Lean closure (Blueprint documents and the
        // like) are not truth nodes, but coverage still accounts for them: their governance state
        // is Semantic, derived from the snapshot rather than from the DAG.
        foreach (var file in snapshot.Files.Keys)
        {
            if (!LeanClosureValidator.IsManagedLean(file.Value)
                && RepositoryPathPolicy.TryResolve(file, out _))
            {
                builder.Add(file, CoverageLedgerState.Semantic);
            }
        }

        return new CoverageLedgerIndex(builder.ToImmutable());
    }

    internal bool TryGet(RepoPath path, out CoverageLedgerState state) =>
        states.TryGetValue(path, out state);
}

public sealed record CoverageMechanisms(
    ImmutableArray<RuleId> ActiveRules,
    ImmutableArray<RuleId> DeferredRules,
    string? ValidationProfile,
    bool MirrorObligation,
    CoverageLedgerState? LedgerState,
    ImmutableArray<string> Registrations)
{
    public bool HasAdjudicator =>
        ActiveRules.Length > 0
        || ValidationProfile is not null
        || MirrorObligation
        || LedgerState is not null
        || Registrations.Length > 0;
}

public sealed record ArtifactCoverage(
    RepoPath Path,
    ArtifactClass Class,
    CoverageMechanisms Mechanisms)
{
    public bool IsUngoverned => !Mechanisms.HasAdjudicator;
}

public sealed record CoverageMatrixRow(
    ArtifactClass Class,
    int Artifacts,
    int Rules,
    int Profiles,
    int Mirrors,
    int Ledger,
    int Registrations,
    int Ungoverned);

public sealed class CoverageReport
{
    internal CoverageReport(
        ImmutableArray<ArtifactCoverage> artifacts,
        ImmutableArray<CoverageMatrixRow> matrix)
    {
        Artifacts = artifacts;
        Matrix = matrix;
        Ungoverned = artifacts.Where(static item => item.IsUngoverned).ToImmutableArray();
    }

    public ImmutableArray<ArtifactCoverage> Artifacts { get; }

    public ImmutableArray<CoverageMatrixRow> Matrix { get; }

    public ImmutableArray<ArtifactCoverage> Ungoverned { get; }
}
