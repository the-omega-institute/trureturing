using System.Collections.Immutable;
using System.Diagnostics;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class TruthGraphJsonTests
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly TruthGraphProvenance Provenance = new(
        "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");

    [Fact]
    public void SnapshotIdentityIsContentAddressedWithoutSelfReferentialProjectionBytes()
    {
        var first = Snapshot(
            ("Meta/source.txt", "alpha\n"),
            (DagEmitter.TruthGraphRelativePath, "old projection\n"));
        var selfChanged = Snapshot(
            ("Meta/source.txt", "alpha\n"),
            (DagEmitter.TruthGraphRelativePath, "new projection\n"));
        var sourceChanged = Snapshot(
            ("Meta/source.txt", "beta\n"),
            (DagEmitter.TruthGraphRelativePath, "old projection\n"));

        Assert.Equal(TruthGraphSnapshotIdentity.Compute(first), TruthGraphSnapshotIdentity.Compute(selfChanged));
        Assert.NotEqual(TruthGraphSnapshotIdentity.Compute(first), TruthGraphSnapshotIdentity.Compute(sourceChanged));
    }

    [Fact]
    public void WriteIsDeterministicCanonicalUtf8AndCarriesEveryTruthFact()
    {
        var dag = Build(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Closed.lean"] = "def closed : Nat := 0\n",
                ["D5/X_Frontier/Openly.lean"] = "def openly : Nat := 0\n",
                ["D5/X_Assumptions/Tailed.lean"] = "axiom tailed : Nat\n",
                ["Meta/notes.md"] = "semantic island\n",
            },
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Closed.lean"] = Report(),
                ["D5/X_Frontier/Openly.lean"] = Report("D5.S0.Carrier.Closed"),
                ["D5/X_Assumptions/Tailed.lean"] = Report("D5.S0.Carrier.Closed"),
            });
        var model = TruthGraphExportModel.Create(dag, Provenance);

        var stopwatch = Stopwatch.StartNew();
        var first = TruthGraphJsonWriter.Write(model);
        stopwatch.Stop();
        var second = TruthGraphJsonWriter.Write(model);

        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        Assert.False(first.AsSpan().StartsWith(new byte[] { 0xEF, 0xBB, 0xBF }));
        var text = StrictUtf8.GetString(first.AsSpan());
        Assert.DoesNotContain('\r', text);
        Assert.EndsWith("\n", text, StringComparison.Ordinal);
        Assert.False(text.EndsWith("\n\n", StringComparison.Ordinal));
        Assert.Equal(dag.Nodes.Length, model.Truth.Nodes.Length);
        Assert.Equal(
            dag.Nodes.Select(static node => node.RepoPath.Value).Order(StringComparer.Ordinal),
            model.Truth.Nodes.Select(static node => node.RepoPath));
        Assert.Equal(model.Truth.Nodes.Length, model.Truth.Nodes.Select(static node => node.RepoPath).Distinct(StringComparer.Ordinal).Count());
        Assert.All(dag.Nodes, source => Assert.Equal(
            source.State.ToString().ToLowerInvariant(),
            model.Truth.Nodes.Single(node => node.RepoPath == source.RepoPath.Value).State));

        var paths = model.Truth.Nodes.Select(static node => node.RepoPath).ToHashSet(StringComparer.Ordinal);
        Assert.All(model.Truth.Edges, edge =>
        {
            Assert.Contains(edge.Dependency, paths);
            Assert.Contains(edge.Dependent, paths);
        });
        Assert.All(model.Truth.OpenBlockers, blocker => Assert.Contains(blocker.Dependent, paths));
        Assert.All(model.Truth.Nodes, node =>
        {
            var dependencies = model.Truth.Edges.Where(edge => edge.Dependent == node.RepoPath).ToArray();
            Assert.Equal(
                dependencies.Length == 0 ? 0 : 1 + dependencies.Max(edge => model.Truth.Nodes.Single(candidate => candidate.RepoPath == edge.Dependency).Depth),
                node.Depth);
        });
        Assert.Equal(dag.RootSha256, model.Provenance.TruthRootSha256);
        Assert.Equal("module-import", model.Provenance.DependencyGranularity);
        Assert.Equal(dag.Nodes.Length, model.Truth.StateCounts.Total);
        Console.WriteLine($"truth-graph baseline: bytes={first.Length}; writer_elapsed_ticks={stopwatch.ElapsedTicks}");
    }

    [Fact]
    public void TwentyInputPermutationsProduceOneByteSequence()
    {
        var modules = Enumerable.Range(0, 8)
            .Select(index => new KeyValuePair<string, string>($"D5/S0/Carrier/M{index}.lean", $"def m{index} : Nat := {index}\n"))
            .Append(new KeyValuePair<string, string>("Meta/island.md", "semantic\n"))
            .ToArray();
        var reports = Enumerable.Range(0, 8).ToDictionary(
            index => $"D5/S0/Carrier/M{index}.lean",
            index => index == 0 ? Report() : Report($"D5.S0.Carrier.M{index - 1}"),
            StringComparer.Ordinal);
        var outputs = new HashSet<string>(StringComparer.Ordinal);
        for (var seed = 0; seed < 20; seed++)
        {
            var random = new Random(seed);
            var shuffled = modules.OrderBy(_ => random.Next()).ToArray();
            var dag = Build(shuffled, reports);
            outputs.Add(Convert.ToBase64String(TruthGraphJsonWriter.Write(TruthGraphExportModel.Create(dag, Provenance)).AsSpan()));
        }

        Assert.Single(outputs);
    }

    [Fact]
    public void StrictReaderRoundTripsEveryCapabilityField()
    {
        var dag = Build(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Delta.lean"] = "def delta : Nat := 0\n",
                ["D5/S0/Carrier/Epsilon.lean"] = "def epsilon : Nat := 0\n",
                ["Meta/no-module-name.md"] = "semantic\n",
            },
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Delta.lean"] = Report(),
                ["D5/S0/Carrier/Epsilon.lean"] = Report("D5.S0.Carrier.Delta", "D5.S0.Carrier.Absent"),
            });
        var expected = TruthGraphExportModel.Create(dag, Provenance);

        var actual = TruthGraphJsonReader.Read(TruthGraphJsonWriter.Write(expected).AsSpan());

        Assert.Equal(expected.Schema, actual.Schema);
        Assert.Equal(expected.SchemaVersion, actual.SchemaVersion);
        Assert.Equal(expected.Provenance, actual.Provenance);
        Assert.True(expected.Truth.Nodes.SequenceEqual(actual.Truth.Nodes));
        Assert.True(expected.Truth.Edges.SequenceEqual(actual.Truth.Edges));
        Assert.True(expected.Truth.OpenBlockers.SequenceEqual(actual.Truth.OpenBlockers));
        Assert.Equal(expected.Truth.StateCounts, actual.Truth.StateCounts);
    }

    [Fact]
    public void EmptyAndSingleNodeGraphsRoundTrip()
    {
        var empty = Build([], new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));
        var single = Build(
            [new KeyValuePair<string, string>("Meta/only.txt", "one\n")],
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));

        Assert.Empty(TruthGraphJsonReader.Read(TruthGraphJsonWriter.Write(TruthGraphExportModel.Create(empty, Provenance)).AsSpan()).Truth.Nodes);
        var node = Assert.Single(TruthGraphJsonReader.Read(TruthGraphJsonWriter.Write(TruthGraphExportModel.Create(single, Provenance)).AsSpan()).Truth.Nodes);
        Assert.Null(node.ModuleName);
        Assert.Equal("semantic", node.State);
        Assert.Equal(0, node.Depth);
    }

    [Theory]
    [InlineData("{}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-graph.v1\",\"schema_version\":1,\"provenance\":{},\"truth\":{},\"extra\":true}\n")]
    [InlineData("{\"schema\":\"wrong\",\"schema_version\":1,\"provenance\":{},\"truth\":{}}\n")]
    public void StrictReaderRejectsMalformedOrUnknownFields(string json) =>
        Assert.Throws<FormatException>(() => TruthGraphJsonReader.Read(Encoding.UTF8.GetBytes(json)));

    private static AcyclicTruthDag Build(
        IEnumerable<KeyValuePair<string, string>> files,
        IReadOnlyDictionary<string, LeanFileReport> reports) =>
        Build(files.ToDictionary(static pair => pair.Key, static pair => pair.Value, StringComparer.Ordinal), reports);

    private static AcyclicTruthDag Build(
        IReadOnlyDictionary<string, string> files,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
        return Assert.IsType<DagBuildOutcome.Accepted>(AcyclicTruthDag.Build(snapshot, closure)).Capability;
    }

    private static LeanFileReport Report(params string[] imports) =>
        new(imports.ToImmutableArray(), ImmutableArray<LeanDeclaration>.Empty);

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(static file => RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;
}
