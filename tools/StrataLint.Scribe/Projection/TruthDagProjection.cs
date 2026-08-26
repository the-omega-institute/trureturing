using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record TruthProjectionNode
{
    private TruthProjectionNode(
        RepoPath repoPath,
        Gid? gid,
        TruthState state,
        string moduleName)
    {
        RepoPath = repoPath;
        Gid = gid;
        State = state;
        ModuleName = moduleName;
    }

    public RepoPath RepoPath { get; }

    public Gid? Gid { get; }

    public TruthState State { get; }

    public string ModuleName { get; }

    internal static TruthProjectionNode Create(
        RepoPath repoPath,
        Gid? gid,
        TruthState state,
        string moduleName) =>
        new(repoPath, gid, state, moduleName);
}

public sealed record TruthProjectionEdge(RepoPath Dependency, RepoPath Dependent);

public sealed record TruthProjectionBlocker(RepoPath Dependent, string DependencyModule);

/// The Scribe-owned, report-derived truth graph used exclusively by graph projections.
/// Lean validation supplies the acyclic language boundary; this class only assembles the
/// deterministic picture consumed by canonical writers.
public sealed class TruthDagProjection
{
    private TruthDagProjection(
        ImmutableArray<TruthProjectionNode> nodes,
        ImmutableArray<TruthProjectionEdge> edges,
        ImmutableArray<TruthProjectionBlocker> openBlockers,
        string rootSha256,
        ImmutableDictionary<RepoPath, int> depths)
    {
        Nodes = nodes;
        Edges = edges;
        OpenBlockers = openBlockers;
        RootSha256 = rootSha256;
        this.depths = depths;
    }

    private readonly ImmutableDictionary<RepoPath, int> depths;

    public ImmutableArray<TruthProjectionNode> Nodes { get; }

    public ImmutableArray<TruthProjectionEdge> Edges { get; }

    public ImmutableArray<TruthProjectionBlocker> OpenBlockers { get; }

    public string RootSha256 { get; }

    public int Depth(RepoPath node) =>
        depths.TryGetValue(node, out var result)
            ? result
            : throw new KeyNotFoundException($"Truth projection does not contain {node.Value}.");

    internal static TruthDagProjection Create(
        ImmutableArray<TruthProjectionNode> nodes,
        ImmutableArray<TruthProjectionEdge> edges,
        ImmutableArray<TruthProjectionBlocker> openBlockers,
        string rootSha256,
        ImmutableDictionary<RepoPath, int> depths) =>
        new(nodes, edges, openBlockers, rootSha256, depths);
}

public static class TruthDagProjectionAssembler
{
    public static TruthDagProjection Build(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);

        var states = LeanTruthStates.Resolve(snapshot, lean);
        return Build(snapshot, lean, states);
    }

    internal static TruthDagProjection Build(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        ImmutableDictionary<RepoPath, TruthState> states)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(states);
        var nodes = snapshot.Files.Keys
            .Where(static path => LeanClosureValidator.IsManagedLean(path.Value))
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .Select(path => CreateNode(snapshot.Files[path], states[path]))
            .ToImmutableArray();
        var pathsByModule = nodes
            .ToImmutableDictionary(static node => node.ModuleName, static node => node.RepoPath, StringComparer.Ordinal);

        var edgeSet = new HashSet<TruthProjectionEdge>();
        var blockerSet = new HashSet<TruthProjectionBlocker>();
        foreach (var node in nodes)
        {
            if (!lean.Report.Files.TryGetValue(node.RepoPath, out var report))
            {
                continue;
            }

            foreach (var importedModule in report.Imports.Distinct(StringComparer.Ordinal))
            {
                if (pathsByModule.TryGetValue(importedModule, out var dependency))
                {
                    edgeSet.Add(new TruthProjectionEdge(dependency, node.RepoPath));
                }
                else if (IsManagedModuleReference(importedModule))
                {
                    blockerSet.Add(new TruthProjectionBlocker(node.RepoPath, importedModule));
                }
            }
        }

        var edges = edgeSet
            .OrderBy(static edge => edge.Dependency.Value, StringComparer.Ordinal)
            .ThenBy(static edge => edge.Dependent.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var blockers = blockerSet
            .OrderBy(static blocker => blocker.Dependent.Value, StringComparer.Ordinal)
            .ThenBy(static blocker => blocker.DependencyModule, StringComparer.Ordinal)
            .ToImmutableArray();
        var mutableDependencies = nodes.ToDictionary(
            static node => node.RepoPath,
            static _ => new List<RepoPath>());
        var mutableDependents = nodes.ToDictionary(
            static node => node.RepoPath,
            static _ => new List<RepoPath>());
        var indegree = nodes.ToDictionary(static node => node.RepoPath, static _ => 0);
        foreach (var edge in edges)
        {
            mutableDependencies[edge.Dependent].Add(edge.Dependency);
            mutableDependents[edge.Dependency].Add(edge.Dependent);
            indegree[edge.Dependent]++;
        }

        var dependencies = mutableDependencies.ToImmutableDictionary(
            static item => item.Key,
            static item => item.Value.OrderBy(static path => path.Value, StringComparer.Ordinal).ToImmutableArray());
        var dependents = mutableDependents.ToImmutableDictionary(
            static item => item.Key,
            static item => item.Value.OrderBy(static path => path.Value, StringComparer.Ordinal).ToImmutableArray());
        var ready = new PriorityQueue<RepoPath, string>(StringComparer.Ordinal);
        foreach (var node in nodes)
        {
            if (indegree[node.RepoPath] == 0)
            {
                ready.Enqueue(node.RepoPath, node.RepoPath.Value);
            }
        }

        var processedNodeCount = 0;
        var mutableDepths = new Dictionary<RepoPath, int>();
        while (ready.TryDequeue(out var path, out _))
        {
            mutableDepths[path] = dependencies[path].Length == 0
                ? 0
                : 1 + dependencies[path].Max(dependency => mutableDepths[dependency]);
            processedNodeCount++;
            foreach (var dependent in dependents[path])
            {
                indegree[dependent]--;
                if (indegree[dependent] == 0)
                {
                    ready.Enqueue(dependent, dependent.Value);
                }
            }
        }

        if (processedNodeCount != nodes.Length)
        {
            throw new InvalidOperationException("Lean truth projection is not topologically ordered.");
        }

        return TruthDagProjection.Create(
            nodes,
            edges,
            blockers,
            ComputeRoot(nodes, edges, blockers),
            mutableDepths.ToImmutableDictionary());
    }

    private static TruthProjectionNode CreateNode(RepositoryFile file, TruthState state)
    {
        var path = file.Path;
        var moduleName = path.Value == "Trureturing.lean"
            ? "Trureturing"
            : path.Value[..^5].Replace('/', '.');
        RepositoryPathPolicy.TryResolve(path, out var gid);
        return TruthProjectionNode.Create(path, gid, state, moduleName);
    }

    private static bool IsManagedModuleReference(string moduleName) =>
        string.Equals(moduleName, "D5", StringComparison.Ordinal)
        || moduleName.StartsWith("D5.", StringComparison.Ordinal)
        || string.Equals(moduleName, "Trureturing", StringComparison.Ordinal);

    private static string ComputeRoot(
        ImmutableArray<TruthProjectionNode> nodes,
        ImmutableArray<TruthProjectionEdge> edges,
        ImmutableArray<TruthProjectionBlocker> blockers)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        AppendString(hash, "stratalint.truth-dag.v1");
        AppendInt32(hash, nodes.Length);
        foreach (var node in nodes)
        {
            AppendString(hash, node.RepoPath.Value);
            AppendString(hash, node.Gid?.Value);
            AppendInt32(hash, (int)node.State);
            AppendString(hash, node.ModuleName);
        }

        AppendInt32(hash, edges.Length);
        foreach (var edge in edges)
        {
            AppendString(hash, edge.Dependency.Value);
            AppendString(hash, edge.Dependent.Value);
        }

        AppendInt32(hash, blockers.Length);
        foreach (var blocker in blockers)
        {
            AppendString(hash, blocker.Dependent.Value);
            AppendString(hash, blocker.DependencyModule);
        }

        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private static void AppendString(IncrementalHash hash, string? value)
    {
        if (value is null)
        {
            AppendInt32(hash, -1);
            return;
        }

        var bytes = Encoding.UTF8.GetBytes(value);
        AppendInt32(hash, bytes.Length);
        hash.AppendData(bytes);
    }

    private static void AppendInt32(IncrementalHash hash, int value)
    {
        Span<byte> bytes = stackalloc byte[sizeof(int)];
        BinaryPrimitives.WriteInt32LittleEndian(bytes, value);
        hash.AppendData(bytes);
    }
}
