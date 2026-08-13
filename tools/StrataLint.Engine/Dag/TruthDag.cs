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

public sealed record TruthStateGroup(TruthState State, ImmutableArray<TruthNode> Nodes);

public sealed record NodeImpact(
    RepoPath Root,
    ImmutableArray<TruthNode> AffectedNodes,
    ImmutableArray<TruthEdge> AffectedEdges,
    ImmutableArray<TruthStateGroup> StateBreakdown);

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
        ImmutableDictionary<RepoPath, TruthNode> nodesByPath,
        ImmutableDictionary<RepoPath, int> depths,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> dependencies,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> dependents)
    {
        Nodes = nodes;
        Edges = edges;
        OpenBlockers = openBlockers;
        RootSha256 = rootSha256;
        TopologicalOrder = topologicalOrder;
        this.nodesByPath = nodesByPath;
        this.depths = depths;
        this.dependencies = dependencies;
        this.dependents = dependents;
    }

    private readonly ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> dependencies;
    private readonly ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> dependents;
    private readonly ImmutableDictionary<RepoPath, TruthNode> nodesByPath;
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

    public ImmutableArray<RepoPath> DependentsOf(RepoPath node) =>
        dependents.TryGetValue(node, out var result)
            ? result
            : throw new KeyNotFoundException($"Truth DAG does not contain {node.Value}.");

    public int Depth(RepoPath node) =>
        depths.TryGetValue(node, out var result)
            ? result
            : throw new KeyNotFoundException($"Truth DAG does not contain {node.Value}.");

    public ImmutableArray<TruthNode> Descendants(RepoPath node)
    {
        if (!dependents.ContainsKey(node))
        {
            throw new KeyNotFoundException($"Truth DAG does not contain {node.Value}.");
        }

        var seen = new HashSet<RepoPath>();
        var pending = new Stack<RepoPath>(dependents[node]);
        while (pending.TryPop(out var current))
        {
            if (!seen.Add(current))
            {
                continue;
            }

            foreach (var dependent in dependents[current])
            {
                pending.Push(dependent);
            }
        }

        return seen
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .Select(path => nodesByPath[path])
            .ToImmutableArray();
    }

    public NodeImpact AnalyzeImpact(RepoPath node)
    {
        if (!nodesByPath.TryGetValue(node, out var root))
        {
            throw new KeyNotFoundException($"Truth DAG does not contain {node.Value}.");
        }

        var affectedNodes = Descendants(node)
            .Append(root)
            .OrderBy(static affected => affected.RepoPath.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var affectedPaths = affectedNodes.Select(static affected => affected.RepoPath).ToHashSet();
        var affectedEdges = Edges
            .Where(edge => affectedPaths.Contains(edge.Dependency) && affectedPaths.Contains(edge.Dependent))
            .ToImmutableArray();
        var breakdown = Enum.GetValues<TruthState>()
            .Select(state => new TruthStateGroup(
                state,
                affectedNodes.Where(node => node.State == state).ToImmutableArray()))
            .ToImmutableArray();
        return new NodeImpact(node, affectedNodes, affectedEdges, breakdown);
    }
}
