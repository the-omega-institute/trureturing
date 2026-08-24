using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

public enum TruthState
{
    Closed,
    Open,
    Tail,
    Semantic,
}

public sealed record TruthNode
{
    private TruthNode(
        RepoPath repoPath,
        Gid? gid,
        TruthState state,
        string? moduleName)
    {
        RepoPath = repoPath;
        Gid = gid;
        State = state;
        ModuleName = moduleName;
    }

    public RepoPath RepoPath { get; }

    public Gid? Gid { get; }

    public TruthState State { get; }

    public string? ModuleName { get; }

    internal static TruthNode Create(
        RepoPath repoPath,
        Gid? gid,
        TruthState state,
        string? moduleName) =>
        new(repoPath, gid, state, moduleName);
}

public sealed record TruthEdge(RepoPath Dependency, RepoPath Dependent);

public sealed record TruthDependencyBlocker(RepoPath Dependent, string DependencyModule);

[Union(EnableImplicitConversions = false)]
public partial record DagBuildOutcome
{
    public partial record Accepted
    {
        internal Accepted(AcyclicTruthDag capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public AcyclicTruthDag Capability { get; }
    }

    public partial record Rejected(ImmutableArray<RepoPath> Witness);
}

public sealed partial class AcyclicTruthDag
{
    private AcyclicTruthDag(
        ImmutableArray<TruthNode> nodes,
        ImmutableArray<TruthEdge> edges,
        ImmutableArray<TruthDependencyBlocker> openBlockers,
        string rootSha256,
        ImmutableArray<TruthNode> topologicalOrder,
        ImmutableDictionary<RepoPath, int> depths,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> dependencies)
    {
        Nodes = nodes;
        Edges = edges;
        OpenBlockers = openBlockers;
        RootSha256 = rootSha256;
        TopologicalOrder = topologicalOrder;
        this.depths = depths;
        this.dependencies = dependencies;
    }

    private readonly ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> dependencies;
    private readonly ImmutableDictionary<RepoPath, int> depths;

    public ImmutableArray<TruthNode> Nodes { get; }

    public ImmutableArray<TruthEdge> Edges { get; }

    public ImmutableArray<TruthDependencyBlocker> OpenBlockers { get; }

    public string RootSha256 { get; }

    public ImmutableArray<TruthNode> TopologicalOrder { get; }

    public ImmutableArray<RepoPath> DependenciesOf(RepoPath node) =>
        dependencies.TryGetValue(node, out var result)
            ? result
            : throw new KeyNotFoundException($"Truth DAG does not contain {node.Value}.");

    public int Depth(RepoPath node) =>
        depths.TryGetValue(node, out var result)
            ? result
            : throw new KeyNotFoundException($"Truth DAG does not contain {node.Value}.");
}
