using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TruthDagTests
{
    [Fact]
    public void StandardAxiomAlphabetIsPinned()
    {
        Assert.Equal(
            new[] { "Classical.choice", "Quot.sound", "propext" },
            LeanAxiomFacts.StandardAxioms.Order(StringComparer.Ordinal));
    }

    [Fact]
    public void TruthNodeStateAndAcyclicDagCannotBeForgedThroughPublicConstructors()
    {
        Assert.Empty(typeof(TruthNode).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(AcyclicTruthDag).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
    }

    [Fact]
    public void StraightChainUsesDependencyToDependentEdgesAndOrdinalTopologicalOrder()
    {
        var dag = BuildAccepted(
            Module("A"),
            Module("B", "A"),
            Module("C", "B"));

        Assert.Equal(
            new[] { PathFor("A"), PathFor("B"), PathFor("C") },
            dag.TopologicalOrder.Select(static node => node.RepoPath.Value));
        Assert.Equal(
            new[]
            {
                $"{PathFor("A")} -> {PathFor("B")}",
                $"{PathFor("B")} -> {PathFor("C")}",
            },
            dag.Edges.Select(static edge => $"{edge.Dependency.Value} -> {edge.Dependent.Value}"));
    }

    [Fact]
    public void DiamondBuildsForwardAndReverseAdjacencyWithoutDuplicatingTheSharedDependent()
    {
        var dag = BuildAccepted(
            Module("A"),
            Module("B", "A"),
            Module("C", "A"),
            Module("D", "B", "C"));

        Assert.Equal(
            new[] { PathFor("B"), PathFor("C") },
            dag.Edges
                .Where(static edge => edge.Dependency.Value == PathFor("A"))
                .Select(static edge => edge.Dependent.Value)
                .Order(StringComparer.Ordinal));
        Assert.Equal(
            new[] { PathFor("B"), PathFor("C") },
            dag.DependenciesOf(RepoPathFor("D")).Select(static path => path.Value));
        Assert.Equal(4, dag.Edges.Length);
    }

    [Fact]
    public void IsolatedNodeHasEmptyAdjacencyAndParticipatesInOrdinalOrdering()
    {
        var dag = BuildAccepted(Module("Z"), Module("A"));

        Assert.Equal(
            new[] { PathFor("A"), PathFor("Z") },
            dag.TopologicalOrder.Select(static node => node.RepoPath.Value));
        Assert.Empty(dag.DependenciesOf(RepoPathFor("Z")));
        Assert.DoesNotContain(dag.Edges, static edge =>
            edge.Dependency.Value == PathFor("Z") || edge.Dependent.Value == PathFor("Z"));
    }

    [Fact]
    public void RepositoryFilesWithoutALeanModuleAreOutsideTheDagDomain()
    {
        const string lean = "D5/S0/Carrier/A.lean";
        const string projection = "Blueprint/D5/S0/Carrier/A.md";
        const string data = "Meta/registry.yaml";
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [lean] = "def a : Nat := 0\n",
            [projection] = "# A\n",
            [data] = "domains: []\n",
        };
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [lean] = Report(),
        };

        var dag = BuildAccepted(files, reports);

        var node = Assert.Single(dag.Nodes);
        Assert.Equal(lean, node.RepoPath.Value);
        Assert.NotNull(node.ModuleName);
    }

    [Fact]
    public void MissingManagedImportIsAnOpenBlockerAndNeverAGuessedEdge()
    {
        var dag = BuildAccepted(Module("A", "Missing"));

        var blocker = Assert.Single(dag.OpenBlockers);
        Assert.Equal(PathFor("A"), blocker.Dependent.Value);
        Assert.Equal(ModuleNameFor("Missing"), blocker.DependencyModule);
        Assert.Empty(dag.Edges);
    }

    [Fact]
    public void StructuralRootIsByteStableAcrossInputEnumerationOrders()
    {
        var first = BuildAccepted(
            Module("A"),
            Module("B", "A"),
            Module("C", "A"),
            Module("D", "B", "C"));
        var second = BuildAccepted(
            Module("D", "C", "B"),
            Module("C", "A"),
            Module("B", "A"),
            Module("A"));

        Assert.Equal(
            Encoding.UTF8.GetBytes(first.RootSha256),
            Encoding.UTF8.GetBytes(second.RootSha256));
        Assert.Matches("^[0-9a-f]{64}$", first.RootSha256);
    }

    [Fact]
    public void CycleRejectionContainsOnlyAnExactClosedEdgeWitness()
    {
        var outcome = BuildOutcome(
            Module("A", "C"),
            Module("B", "A"),
            Module("C", "B"),
            Module("D", "C"));

        var rejected = Assert.IsType<DagBuildOutcome.Rejected>(outcome);
        Assert.Equal(
            new[] { PathFor("A"), PathFor("B"), PathFor("C"), PathFor("A") },
            rejected.Witness.Select(static path => path.Value));
    }

    [Fact]
    public void DepthMatchesBruteForceOnAFixedDag()
    {
        var dag = BuildAccepted(
            Module("A"),
            Module("B", "A"),
            Module("C", "A"),
            Module("D", "B", "C"),
            Module("E", "B"),
            Module("F", "C"),
            Module("G", "D", "E"),
            Module("H"));

        foreach (var node in dag.Nodes)
        {
            Assert.Equal(BruteForceDepth(node.RepoPath, dag.Edges), dag.Depth(node.RepoPath));
        }
    }

    [Fact]
    public void DerivesTruthStatesAndCanonicalGidsOnlyFromRepositoryAndLeanFacts()
    {
        const string closed = "D5/S0/Carrier/ClosedFact.lean";
        const string frontier = "D5/X_Frontier/OpenProblem.lean";
        const string sorry = "D5/S0/Carrier/SorryFact.lean";
        const string task = "D5/S0/Carrier/TaskFact.lean";
        const string debt = "D5/X_Assumptions/AxiomDebt.lean";
        const string conditional = "D5/X_Certificates/ConditionalResult.lean";
        const string semantic = "Blueprint/D5/S0/Carrier/ClosedFact.md";
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [closed] = "theorem closedFact : True := True.intro\n",
            [frontier] = "def openProblem : Nat := 0\n",
            [sorry] = "theorem sorryFact : True := by sorry\n",
            [task] = "/- TASK D5-T9999 -/\ndef taskFact : Nat := 0\n",
            [debt] = "axiom registeredDebt : False\n",
            [conditional] = "theorem conditionalResult : False := registeredDebt\n",
            [semantic] = "# Closed fact\n",
        };
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [closed] = Report(declarations: new[]
            {
                Declaration("closedFact", "propext", "Classical.choice", "Quot.sound"),
            }),
            [frontier] = Report(),
            [sorry] = Report(declarations: new[] { Declaration("sorryFact", "sorryAx") }),
            [task] = Report(),
            [debt] = Report(declarations: new[]
            {
                Declaration("registeredDebt", "registeredDebt", kind: "axiom"),
            }),
            [conditional] = Report(
                imports: new[] { "D5.X_Assumptions.AxiomDebt" },
                declarations: new[] { Declaration("conditionalResult", "registeredDebt") }),
        };

        var dag = BuildAccepted(files, reports);

        Assert.Equal(TruthState.Closed, Node(closed).State);
        Assert.Equal(TruthState.Open, Node(frontier).State);
        Assert.Equal(TruthState.Open, Node(sorry).State);
        Assert.Equal(TruthState.Open, Node(task).State);
        Assert.Equal(TruthState.Tail, Node(debt).State);
        Assert.Equal(TruthState.Tail, Node(conditional).State);
        Assert.DoesNotContain(dag.Nodes, node => node.RepoPath.Value == semantic);
        Assert.Equal("D5/S0/Carrier/ClosedFact", Node(closed).Gid?.Value);

        TruthNode Node(string path) => dag.Nodes.Single(node => node.RepoPath.Value == path);
    }

    private static ModuleSpec Module(string name, params string[] imports) => new(name, imports);

    private static AcyclicTruthDag BuildAccepted(params ModuleSpec[] modules)
    {
        return Assert.IsType<DagBuildOutcome.Accepted>(BuildOutcome(modules)).Capability;
    }

    private static DagBuildOutcome BuildOutcome(params ModuleSpec[] modules)
    {
        var files = modules.ToDictionary(
            static module => PathFor(module.Name),
            static module => $"def {module.Name.ToLowerInvariant()} : Nat := 0\n",
            StringComparer.Ordinal);
        var reports = modules.ToDictionary(
            static module => PathFor(module.Name),
            static module => new LeanFileReport(
                module.Imports.Select(ModuleNameFor).ToImmutableArray(),
                ImmutableArray<LeanDeclaration>.Empty),
            StringComparer.Ordinal);
        return BuildOutcome(files, reports);
    }

    private static AcyclicTruthDag BuildAccepted(
        IReadOnlyDictionary<string, string> files,
        IReadOnlyDictionary<string, LeanFileReport> reports) =>
        Assert.IsType<DagBuildOutcome.Accepted>(BuildOutcome(files, reports)).Capability;

    private static DagBuildOutcome BuildOutcome(
        IReadOnlyDictionary<string, string> files,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;

        return AcyclicTruthDag.Build(snapshot, closure);
    }

    private static string PathFor(string module) => $"D5/S0/Carrier/{module}.lean";

    private static RepoPath RepoPathFor(string module) =>
        RepoPathForPath(PathFor(module));

    private static RepoPath RepoPathForPath(string value) =>
        RepoPath.TryCreate(value, out var path)
            ? path
            : throw new InvalidOperationException("test path is invalid");

    private static string ModuleNameFor(string module) => $"D5.S0.Carrier.{module}";

    private static LeanFileReport Report(
        IEnumerable<string>? imports = null,
        IEnumerable<LeanDeclaration>? declarations = null) =>
        new(
            (imports ?? Array.Empty<string>()).ToImmutableArray(),
            (declarations ?? Array.Empty<LeanDeclaration>()).ToImmutableArray());

    private static LeanDeclaration Declaration(
        string name,
        string axiom,
        string? secondAxiom = null,
        string? thirdAxiom = null,
        string kind = "theorem") =>
        new(
            name,
            kind,
            "True",
            new[] { axiom, secondAxiom, thirdAxiom }
                .OfType<string>()
                .ToImmutableArray());

    private static int BruteForceDepth(RepoPath node, ImmutableArray<TruthEdge> edges)
    {
        var dependencies = edges
            .Where(edge => edge.Dependent == node)
            .Select(static edge => edge.Dependency)
            .ToArray();
        return dependencies.Length == 0
            ? 0
            : 1 + dependencies.Max(dependency => BruteForceDepth(dependency, edges));
    }

    private sealed record ModuleSpec(string Name, IReadOnlyList<string> Imports);
}
