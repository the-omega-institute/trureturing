using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class LeanAxiomFacts
{
    private static readonly ImmutableHashSet<string> StandardAxioms =
        ImmutableHashSet.Create(StringComparer.Ordinal, "propext", "Classical.choice", "Quot.sound");

    internal static bool IsStandard(string axiom) => StandardAxioms.Contains(axiom);
}

public sealed partial class AcyclicTruthDag
{
    private static readonly Regex TaskTokenPattern = new(
        "(?:^|[^A-Za-z0-9_])TASK\\s+D[0-9]+-T[0-9]{4}(?:[^A-Za-z0-9_]|$)",
        RegexOptions.CultureInvariant);

    public static DagBuildOutcome Build(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);

        var nodes = snapshot.Files.Keys
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .Select(path => CreateNode(snapshot.Files[path], lean.Report))
            .ToImmutableArray();
        var nodesByPath = nodes.ToImmutableDictionary(static node => node.RepoPath);
        var pathsByModule = nodes
            .Where(static node => node.ModuleName is not null)
            .ToImmutableDictionary(static node => node.ModuleName!, static node => node.RepoPath, StringComparer.Ordinal);

        // Module imports are a safe over-approximation of declaration dependencies. A declaration-level
        // upgrade remains open until an olean freshness gate exists and DefinitionVal.all mutual groups
        // are unioned before SCC condensation.
        var edgeSet = new HashSet<TruthEdge>();
        var blockerSet = new HashSet<TruthDependencyBlocker>();
        foreach (var node in nodes.Where(static node => node.ModuleName is not null))
        {
            var report = lean.Report.Files[node.RepoPath];
            foreach (var importedModule in report.Imports.Distinct(StringComparer.Ordinal))
            {
                if (pathsByModule.TryGetValue(importedModule, out var dependency))
                {
                    edgeSet.Add(new TruthEdge(dependency, node.RepoPath));
                }
                else if (IsManagedModuleReference(importedModule))
                {
                    blockerSet.Add(new TruthDependencyBlocker(node.RepoPath, importedModule));
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

        var topological = ImmutableArray.CreateBuilder<TruthNode>(nodes.Length);
        var mutableDepths = new Dictionary<RepoPath, int>();
        while (ready.TryDequeue(out var path, out _))
        {
            mutableDepths[path] = dependencies[path].Length == 0
                ? 0
                : 1 + dependencies[path].Max(dependency => mutableDepths[dependency]);
            topological.Add(nodesByPath[path]);
            foreach (var dependent in dependents[path])
            {
                indegree[dependent]--;
                if (indegree[dependent] == 0)
                {
                    ready.Enqueue(dependent, dependent.Value);
                }
            }
        }

        if (topological.Count != nodes.Length)
        {
            return new DagBuildOutcome.Rejected(FindCycle(nodes, dependents, indegree));
        }

        return new DagBuildOutcome.Accepted(new AcyclicTruthDag(
            nodes,
            edges,
            blockers,
            ComputeRoot(nodes, edges, blockers),
            topological.MoveToImmutable(),
            nodesByPath,
            mutableDepths.ToImmutableDictionary(),
            dependencies,
            dependents));
    }

    private static TruthNode CreateNode(RepositoryFile file, LeanAxiomReport report)
    {
        var path = file.Path;
        var moduleName = LeanClosureValidator.IsManagedLean(path.Value)
            ? path.Value == "Trureturing.lean"
                ? "Trureturing"
                : path.Value[..^5].Replace('/', '.')
            : null;
        RepositoryPathPolicy.TryResolve(path, out var gid);
        var state = DeriveState(file, moduleName, report);
        return TruthNode.Create(path, gid, state, moduleName);
    }

    private static TruthState DeriveState(
        RepositoryFile file,
        string? moduleName,
        LeanAxiomReport report)
    {
        if (moduleName is null)
        {
            return TruthState.Semantic;
        }

        var leanFile = report.Files[file.Path];
        if (file.Path.Value.Contains("/X_Frontier/", StringComparison.Ordinal)
            || TaskTokenPattern.IsMatch(file.Text)
            || leanFile.Declarations.Any(static declaration =>
                declaration.Axioms.Contains("sorryAx", StringComparer.Ordinal)))
        {
            return TruthState.Open;
        }

        if (file.Path.Value.Contains("/X_Assumptions/", StringComparison.Ordinal)
            || leanFile.Declarations.Any(static declaration => declaration.Kind == "axiom")
            || leanFile.Declarations.SelectMany(static declaration => declaration.Axioms)
                .Any(static axiom => axiom != "sorryAx" && !LeanAxiomFacts.IsStandard(axiom)))
        {
            return TruthState.Tail;
        }

        return TruthState.Closed;
    }

    private static bool IsManagedModuleReference(string moduleName) =>
        string.Equals(moduleName, "D5", StringComparison.Ordinal)
        || moduleName.StartsWith("D5.", StringComparison.Ordinal)
        || string.Equals(moduleName, "Trureturing", StringComparison.Ordinal);

    private static ImmutableArray<RepoPath> FindCycle(
        ImmutableArray<TruthNode> nodes,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> dependents,
        IReadOnlyDictionary<RepoPath, int> remainingIndegree)
    {
        var remaining = remainingIndegree
            .Where(static item => item.Value > 0)
            .Select(static item => item.Key)
            .ToHashSet();
        var colors = nodes.ToDictionary(static node => node.RepoPath, static _ => (byte)0);
        var parents = new Dictionary<RepoPath, RepoPath>();
        foreach (var start in remaining.OrderBy(static path => path.Value, StringComparer.Ordinal))
        {
            if (colors[start] != 0)
            {
                continue;
            }

            colors[start] = 1;
            var stack = new List<(RepoPath Node, int NextChild)> { (start, 0) };
            while (stack.Count > 0)
            {
                var frameIndex = stack.Count - 1;
                var (node, nextChild) = stack[frameIndex];
                var children = dependents[node];
                while (nextChild < children.Length && !remaining.Contains(children[nextChild]))
                {
                    nextChild++;
                }

                if (nextChild == children.Length)
                {
                    colors[node] = 2;
                    stack.RemoveAt(frameIndex);
                    continue;
                }

                var child = children[nextChild];
                stack[frameIndex] = (node, nextChild + 1);
                if (colors[child] == 0)
                {
                    parents[child] = node;
                    colors[child] = 1;
                    stack.Add((child, 0));
                    continue;
                }

                if (colors[child] == 1)
                {
                    var reverse = new List<RepoPath> { node };
                    while (reverse[^1] != child)
                    {
                        reverse.Add(parents[reverse[^1]]);
                    }

                    reverse.Reverse();
                    reverse.Add(child);
                    return CanonicalizeCycle(reverse);
                }
            }
        }

        throw new InvalidOperationException("Kahn rejected the truth graph without a directed cycle witness.");
    }

    private static ImmutableArray<RepoPath> CanonicalizeCycle(IReadOnlyList<RepoPath> witness)
    {
        var cycleLength = witness.Count - 1;
        var first = 0;
        for (var index = 1; index < cycleLength; index++)
        {
            if (StringComparer.Ordinal.Compare(witness[index].Value, witness[first].Value) < 0)
            {
                first = index;
            }
        }

        var canonical = ImmutableArray.CreateBuilder<RepoPath>(witness.Count);
        for (var offset = 0; offset < cycleLength; offset++)
        {
            canonical.Add(witness[(first + offset) % cycleLength]);
        }

        canonical.Add(canonical[0]);
        return canonical.MoveToImmutable();
    }

    private static string ComputeRoot(
        ImmutableArray<TruthNode> nodes,
        ImmutableArray<TruthEdge> edges,
        ImmutableArray<TruthDependencyBlocker> blockers)
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
