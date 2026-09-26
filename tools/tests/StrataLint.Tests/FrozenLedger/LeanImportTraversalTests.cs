using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanImportTraversalTests
{
    private static RepoPath Path(string name) => RepoPath.CreateKnown($"D5/S0/Carrier/{name}.lean");

    [Fact]
    public void EveryThreeVertexGraphEnumeratesExactlyItsReachableVertices()
    {
        var vertices = new[] { Path("A"), Path("B"), Path("C") };
        // Independent Boolean transitive closure, including positive-length cycles.
        // 2^9 directed graphs (loops allowed), each with all 2^3 root subsets.
        for (var edges = 0; edges < 1 << (vertices.Length * vertices.Length); edges++)
        {
            var reachable = new bool[vertices.Length, vertices.Length];
            var adjacency = new Dictionary<RepoPath, ImmutableArray<RepoPath>>();
            for (var from = 0; from < vertices.Length; from++)
            {
                var children = ImmutableArray.CreateBuilder<RepoPath>();
                for (var to = 0; to < vertices.Length; to++)
                {
                    reachable[from, to] = (edges & (1 << (from * vertices.Length + to))) != 0;
                    if (reachable[from, to])
                    {
                        children.Add(vertices[to]);
                    }
                }
                adjacency.Add(vertices[from], children.ToImmutable());
            }

            for (var via = 0; via < vertices.Length; via++)
            for (var from = 0; from < vertices.Length; from++)
            for (var to = 0; to < vertices.Length; to++)
            {
                reachable[from, to] |= reachable[from, via] && reachable[via, to];
            }

            for (var rootsMask = 0; rootsMask < 1 << vertices.Length; rootsMask++)
            {
                var roots = Enumerable.Range(0, vertices.Length)
                    .Where(root => (rootsMask & (1 << root)) != 0).ToArray();
                var expected = Enumerable.Range(0, vertices.Length)
                    .Where(vertex => roots.Any(root => root == vertex || reachable[root, vertex]))
                    .ToArray();
                var actual = LeanImportAdjacency.DependenciesFirst(
                    roots.Reverse().Select(root => vertices[root]), adjacency);
                var context = $"edges={edges}, roots={rootsMask}";
                Assert.True(actual.Length == actual.Distinct().Count(), context);
                Assert.True(actual.ToHashSet().SetEquals(expected.Select(vertex => vertices[vertex])), context);

                // Cycles outside the reachable set do not prevent a valid order.
                if (expected.All(vertex => !reachable[vertex, vertex]))
                {
                    foreach (var dependent in expected)
                    foreach (var dependency in adjacency[vertices[dependent]])
                    {
                        Assert.True(actual.IndexOf(dependency) < actual.IndexOf(vertices[dependent]), context);
                    }
                }
            }
        }
    }

    [Fact]
    public void RootsUseOrdinalOrderAndAdjacencyKeepsItsSuppliedOrder()
    {
        var root = Path("Root");
        var upper = Path("Z");
        var lower = Path("a");
        Assert.Equal(new[] { upper, lower }, LeanImportAdjacency.DependenciesFirst(
            new[] { lower, upper }, new Dictionary<RepoPath, ImmutableArray<RepoPath>>()));
        Assert.Equal(new[] { lower, upper, root }, LeanImportAdjacency.DependenciesFirst(
            new[] { root }, new Dictionary<RepoPath, ImmutableArray<RepoPath>>
            {
                [root] = [lower, upper],
            }));
    }

    [Fact]
    public void DuplicateRootsEdgesAndSharedDescendantsAreEmittedOnce()
    {
        var a = Path("A");
        var b = Path("B");
        var c = Path("C");
        var d = Path("D");
        var adjacency = new Dictionary<RepoPath, ImmutableArray<RepoPath>>
        {
            [a] = [c, b, c],
            [b] = [d, d],
            [c] = [d],
        };
        Assert.Equal(new[] { d, c, b, a }, LeanImportAdjacency.DependenciesFirst(
            new[] { b, a, a, c }, adjacency));
    }

    [Fact]
    public void MissingDictionaryKeysAreLeavesAndUnreachableEntriesAreOmitted()
    {
        var root = Path("Root");
        var leaf = Path("Leaf");
        var isolated = Path("Isolated");
        var adjacency = new Dictionary<RepoPath, ImmutableArray<RepoPath>>
        {
            [root] = [leaf],
            [isolated] = [isolated],
        };
        Assert.Equal(new[] { leaf, root }, LeanImportAdjacency.DependenciesFirst(new[] { root }, adjacency));
        Assert.Equal(new[] { leaf }, LeanImportAdjacency.DependenciesFirst(new[] { leaf }, adjacency));
        Assert.Empty(LeanImportAdjacency.DependenciesFirst(Array.Empty<RepoPath>(), adjacency));
    }

    [Fact]
    public void CyclesCompleteWithUniquePostorderWithoutClaimingTopologicalOrder()
    {
        var a = Path("A");
        var b = Path("B");
        Assert.Equal(new[] { a }, LeanImportAdjacency.DependenciesFirst(new[] { a },
            new Dictionary<RepoPath, ImmutableArray<RepoPath>> { [a] = [a] }));
        Assert.Equal(new[] { b, a }, LeanImportAdjacency.DependenciesFirst(new[] { a },
            new Dictionary<RepoPath, ImmutableArray<RepoPath>> { [a] = [b], [b] = [a] }));
    }
}
