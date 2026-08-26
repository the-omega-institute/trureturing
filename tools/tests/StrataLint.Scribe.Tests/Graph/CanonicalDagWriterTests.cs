using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class CanonicalDagWriterTests
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    [Fact]
    public void WriteIsByteDeterministic()
    {
        var dag = Build(
            Module("Delta"),
            Module("Epsilon", "Delta"));

        var first = CanonicalDagWriter.Write(dag);
        var second = CanonicalDagWriter.Write(dag);

        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
    }

    [Fact]
    public void ProjectionIsUtf8WithoutBomAndEndsWithASingleNewline()
    {
        var bytes = CanonicalDagWriter.Write(Build(Module("Delta")));

        Assert.False(bytes.Length >= 3 && bytes[0] == 0xEF && bytes[1] == 0xBB && bytes[2] == 0xBF);
        var text = StrictUtf8.GetString(bytes.AsSpan());
        Assert.DoesNotContain('\r', text);
        Assert.EndsWith("\n", text, StringComparison.Ordinal);
        Assert.DoesNotContain("\n\n\n", text, StringComparison.Ordinal);
    }

    [Fact]
    public void EmitsAMermaidFlowchartCarryingEveryFormalNodeAndEdge()
    {
        var dag = Build(
            Module("Delta"),
            Module("Epsilon", "Delta"),
            Module("Zeta", "Delta", "Epsilon"));
        var text = Render(dag);

        Assert.Contains("```mermaid\n", text, StringComparison.Ordinal);
        Assert.Contains("flowchart", text, StringComparison.Ordinal);
        foreach (var node in dag.Nodes)
        {
            Assert.Contains(node.RepoPath.Value, text, StringComparison.Ordinal);
        }

        // One arrow per DAG edge: the fence must not silently drop or invent dependencies.
        var arrows = Fence(text).Split('\n').Count(line => line.Contains("-->", StringComparison.Ordinal));
        Assert.Equal(dag.Edges.Length, arrows);
    }

    [Fact]
    public void NonLeanRepositoryFilesAreAbsentFromTheProjection()
    {
        // The DAG's domain is the managed Lean closure, so a repository file without a Lean
        // module never reaches the writer at all; the census states zero semantic nodes
        // instead of disclosing a truncation.
        var dag = BuildFrom(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Delta.lean"] = "def delta : Nat := 0\n",
                ["Meta/notes.md"] = "not part of the proof topology\n",
            },
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Delta.lean"] = Report(),
            });
        var text = Render(dag);
        var fence = Fence(text);

        Assert.Contains("D5/S0/Carrier/Delta.lean", fence, StringComparison.Ordinal);
        Assert.DoesNotContain("Meta/notes.md", text, StringComparison.Ordinal);
        Assert.Contains("semantic 0", text, StringComparison.Ordinal);
        Assert.Contains("- nodes: 1 total\n", text, StringComparison.Ordinal);
    }

    [Fact]
    public void ArrowsRunFromDependencyToDependent()
    {
        var dag = Build(
            Module("Delta"),
            Module("Epsilon", "Delta"));
        var fence = Fence(Render(dag));

        var rootId = IdentifierFor(fence, "D5/S0/Carrier/Delta.lean");
        var leafId = IdentifierFor(fence, "D5/S0/Carrier/Epsilon.lean");

        Assert.Contains($"{rootId} --> {leafId}", fence, StringComparison.Ordinal);
        Assert.DoesNotContain($"{leafId} --> {rootId}", fence, StringComparison.Ordinal);
    }

    [Fact]
    public void NodeIdentifiersAreUniqueAcrossPathsThatCollideUnderNaiveEscaping()
    {
        // "A/B.lean" and "A_B.lean" both become "A_B_lean" if the writer just replaces
        // separators; a collision would merge two truth nodes into one graph vertex.
        var dag = BuildFrom(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/A/B.lean"] = "def ab : Nat := 0\n",
                ["D5/S0/Carrier/A_B.lean"] = "def a_b : Nat := 0\n",
            },
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/A/B.lean"] = Report(),
                ["D5/S0/Carrier/A_B.lean"] = Report(),
            });
        var fence = Fence(Render(dag));

        var first = IdentifierFor(fence, "D5/S0/Carrier/A/B.lean");
        var second = IdentifierFor(fence, "D5/S0/Carrier/A_B.lean");

        Assert.NotEqual(first, second);
    }

    [Fact]
    public void SummaryRecordsTheContentAddressAndTheStateCensus()
    {
        var dag = Build(
            Module("Delta"),
            Module("Epsilon", "Delta"));
        var text = Render(dag);

        Assert.Contains(dag.RootSha256, text, StringComparison.Ordinal);
        Assert.Contains(dag.Nodes.Length.ToString(), text, StringComparison.Ordinal);
        foreach (var state in Enum.GetValues<TruthState>())
        {
            Assert.Contains(state.ToString().ToLowerInvariant(), text, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void NodesAreGroupedByGraphDepth()
    {
        var dag = Build(
            Module("Delta"),
            Module("Epsilon", "Delta"),
            Module("Zeta", "Epsilon"));
        var text = Render(dag);

        // depth(Delta)=0, depth(Epsilon)=1, depth(Zeta)=2 — the writer must expose the
        // longest-dependency-path depth, not an arbitrary topological index.
        Assert.Equal(0, dag.Depth(PathOf(dag, "Delta")));
        Assert.Equal(1, dag.Depth(PathOf(dag, "Epsilon")));
        Assert.Equal(2, dag.Depth(PathOf(dag, "Zeta")));
        Assert.Contains("depth 0", text, StringComparison.Ordinal);
        Assert.Contains("depth 1", text, StringComparison.Ordinal);
        Assert.Contains("depth 2", text, StringComparison.Ordinal);
        Assert.True(
            text.IndexOf("depth 0", StringComparison.Ordinal)
            < text.IndexOf("depth 1", StringComparison.Ordinal));
    }

    [Fact]
    public void EveryTruthStateIsRenderedDistinctly()
    {
        var dag = BuildFrom(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Closed.lean"] = "def closed : Nat := 0\n",
                ["D5/X_Frontier/Openly.lean"] = "def openly : Nat := 0\n",
                ["D5/X_Assumptions/Tailed.lean"] = "def tailed : Nat := 0\n",
            },
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Closed.lean"] = Report(),
                ["D5/X_Frontier/Openly.lean"] = Report(),
                ["D5/X_Assumptions/Tailed.lean"] = Report(),
            });
        var text = Render(dag);

        Assert.Equal(
            [TruthState.Closed, TruthState.Open, TruthState.Tail],
            dag.Nodes.Select(static node => node.State).Distinct().Order().ToArray());
        foreach (var state in Enum.GetValues<TruthState>())
        {
            Assert.Contains(
                "classDef " + state.ToString().ToLowerInvariant(),
                text,
                StringComparison.Ordinal);
        }
    }

    [Fact]
    public void OpenDependencyBlockersAreDisclosedRatherThanDropped()
    {
        // An import of a managed module that is not in the snapshot is a real hole in the
        // graph. Rendering it silently as "no edge" would make the picture look complete.
        var dag = BuildFrom(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Delta.lean"] = "def delta : Nat := 0\n",
            },
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Delta.lean"] = Report("D5.S0.Carrier.Absent"),
            });
        var text = Render(dag);

        Assert.NotEmpty(dag.OpenBlockers);
        Assert.Contains("D5.S0.Carrier.Absent", text, StringComparison.Ordinal);
    }

    [Fact]
    public void NodesAndEdgesAreOrderedOrdinallyRegardlessOfInputOrder()
    {
        var forward = Build(
            Module("Alpha"),
            Module("Beta", "Alpha"),
            Module("Gamma", "Alpha"));
        var reversed = Build(
            Module("Gamma", "Alpha"),
            Module("Beta", "Alpha"),
            Module("Alpha"));

        Assert.True(
            CanonicalDagWriter.Write(forward).AsSpan()
                .SequenceEqual(CanonicalDagWriter.Write(reversed).AsSpan()));
    }

    private static string Render(TruthDagProjection dag) =>
        StrictUtf8.GetString(CanonicalDagWriter.Write(dag).AsSpan());

    private static string Fence(string text)
    {
        var start = text.IndexOf("```mermaid\n", StringComparison.Ordinal);
        Assert.True(start >= 0, "projection has no mermaid fence");
        start += "```mermaid\n".Length;
        var end = text.IndexOf("```", start, StringComparison.Ordinal);
        Assert.True(end > start, "mermaid fence is unterminated");
        return text[start..end];
    }

    /// The mermaid identifier the writer assigned to a repository path, read back out of the
    /// fence so the tests assert on the rendered graph rather than on a private naming rule.
    private static string IdentifierFor(string fence, string repoPath)
    {
        var line = fence.Split('\n')
            .FirstOrDefault(candidate => candidate.Contains(
                "\"" + repoPath + "\"",
                StringComparison.Ordinal));
        Assert.NotNull(line);
        var trimmed = line.TrimStart();
        var stop = trimmed.IndexOfAny(['[', '(', '{', ' ']);
        Assert.True(stop > 0, "node declaration has no identifier: " + line);
        return trimmed[..stop];
    }

    private static RepoPath PathOf(TruthDagProjection dag, string module) =>
        dag.Nodes.Single(node => node.RepoPath.Value.EndsWith(
            "/" + module + ".lean",
            StringComparison.Ordinal)).RepoPath;

    private static ModuleSpec Module(string name, params string[] imports) => new(name, imports);

    private static TruthDagProjection Build(params ModuleSpec[] modules)
    {
        var files = modules.ToDictionary(
            static module => "D5/S0/Carrier/" + module.Name + ".lean",
            static module => $"def {module.Name.ToLowerInvariant()} : Nat := 0\n",
            StringComparer.Ordinal);
        var reports = modules.ToDictionary(
            static module => "D5/S0/Carrier/" + module.Name + ".lean",
            static module => Report(
                module.Imports.Select(static name => "D5.S0.Carrier." + name).ToArray()),
            StringComparer.Ordinal);
        return BuildFrom(files, reports);
    }

    private static TruthDagProjection BuildFrom(
        IReadOnlyDictionary<string, string> files,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var raw = RawRepositorySnapshot.Create(
            files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
        return TruthDagProjectionAssembler.Build(snapshot, closure);
    }

    private static LeanFileReport Report(params string[] imports) =>
        new(imports.ToImmutableArray(), ImmutableArray<LeanDeclaration>.Empty);

    private sealed record ModuleSpec(string Name, string[] Imports);
}
