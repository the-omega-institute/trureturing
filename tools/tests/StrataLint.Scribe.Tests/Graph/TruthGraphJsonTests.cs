using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe.Tests;

public sealed class TruthGraphJsonTests
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly TruthGraphProvenance Provenance = new(
        "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");

    [Fact]
    public void SnapshotIdentityIgnoresAllGeneratedProjectionBytes()
    {
        var documentPath = DocumentDefinitions.All[0].RelativePath.Value;
        var first = Snapshot(
            ("Meta/source.txt", "alpha\n"),
            (documentPath, "old document projection\n"),
            (DagEmitter.RelativePath, "old dag projection\n"),
            (DagEmitter.TruthGraphRelativePath, "old truth projection\n"),
            (ScribeEmitter.AttestationRelativePath, "old attestation\n"));
        var projectionsChanged = Snapshot(
            ("Meta/source.txt", "alpha\n"),
            (documentPath, "new document projection\n"),
            (DagEmitter.RelativePath, "new dag projection\n"),
            (DagEmitter.TruthGraphRelativePath, "new truth projection\n"),
            (ScribeEmitter.AttestationRelativePath, "new attestation\n"));
        var sourceChanged = Snapshot(
            ("Meta/source.txt", "beta\n"),
            (documentPath, "old document projection\n"),
            (DagEmitter.RelativePath, "old dag projection\n"),
            (DagEmitter.TruthGraphRelativePath, "old truth projection\n"),
            (ScribeEmitter.AttestationRelativePath, "old attestation\n"));

        Assert.Equal(
            SnapshotContentDigest.Compute(first),
            SnapshotContentDigest.Compute(projectionsChanged));
        Assert.NotEqual(SnapshotContentDigest.Compute(first), SnapshotContentDigest.Compute(sourceChanged));
    }

    [Fact]
    public void WriteIsDeterministicCanonicalUtf8AndCarriesEveryTruthFact()
    {
        var dag = BuildFromFiles(
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
        var model = TruthGraphModelBuilder.Create(dag, Provenance);

        var first = TruthGraphJsonWriter.Write(model);
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
        var inputs = new HashSet<string>(StringComparer.Ordinal);
        int[] multipliers = [1, 2, 4, 5];
        for (var permutation = 0; permutation < 20; permutation++)
        {
            var multiplier = multipliers[permutation % multipliers.Length];
            var offset = permutation / 4;
            var shuffled = modules
                .Select((module, index) => (Module: module, Key: (index * multiplier + offset) % modules.Length))
                .OrderBy(static item => item.Key)
                .Select(static item => item.Module)
                .ToArray();
            inputs.Add(string.Join('\n', shuffled.Select(static module => module.Key)));
            var dag = BuildFromEntries(shuffled, reports);
            outputs.Add(Convert.ToBase64String(TruthGraphJsonWriter.Write(TruthGraphModelBuilder.Create(dag, Provenance)).AsSpan()));
        }

        Assert.Equal(20, inputs.Count);
        Assert.Single(outputs);
    }

    [Fact]
    public void DocumentLayersKeepLoadBearingAndNarrativeEdgesSeparateAndJoinEveryAnchor()
    {
        var declaration = LeanDeclarationRef.Create("D5/S0/Carrier/Target.anchor");
        var source = Document(
            "D5/S0/Carrier/Source",
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Carrier/Target")),
                DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S0/Carrier/Target")),
                DocumentEdge.TruthAnchor.Create(declaration),
            ]);
        var target = Document("D5/S0/Carrier/Target");
        var reportFiles = new Dictionary<string, LeanFileReport>
        {
            ["D5/S0/Carrier/Target.lean"] = new([], [new LeanDeclaration(
                "D5.S0.Carrier.Target.anchor", "theorem", "True", [])]),
        };
        var report = LeanAxiomReport.Create(reportFiles);
        var catalog = DeclarationCatalog.Create(report);
        var graph = DocumentGraphAssembler.Assemble([target, source], catalog);
        Assert.Empty(graph.Findings);
        var documents = DocumentGraphExportProjection.Create(
            [
                new DocumentGraphDocument("Blueprint/D5/S0/Carrier/Target.md", target, "receipt-bound"),
                new DocumentGraphDocument("Blueprint/D5/S0/Carrier/Source.md", source, "receipt-free"),
            ],
            graph,
            catalog,
            new HashSet<string>(["D5/S0/Carrier/Target.lean"], StringComparer.Ordinal));
        var model = TruthGraphModelBuilder.Create(BuildFromFiles(
            new Dictionary<string, string> { ["D5/S0/Carrier/Target.lean"] = "theorem anchor : True := True.intro\n" },
            reportFiles), Provenance, documents);
        var reorderedDocuments = DocumentGraphExportProjection.Create(
            [
                new DocumentGraphDocument("Blueprint/D5/S0/Carrier/Source.md", source, "receipt-free"),
                new DocumentGraphDocument("Blueprint/D5/S0/Carrier/Target.md", target, "receipt-bound"),
            ],
            DocumentGraphAssembler.Assemble([source, target], catalog),
            catalog,
            new HashSet<string>(["D5/S0/Carrier/Target.lean"], StringComparer.Ordinal));
        var reorderedModel = TruthGraphModelBuilder.Create(BuildFromFiles(
            new Dictionary<string, string> { ["D5/S0/Carrier/Target.lean"] = "theorem anchor : True := True.intro\n" },
            reportFiles), Provenance, reorderedDocuments);
        Assert.True(TruthGraphJsonWriter.Write(model).AsSpan()
            .SequenceEqual(TruthGraphJsonWriter.Write(reorderedModel).AsSpan()));

        var dependency = Assert.Single(model.Documents.DependencyEdges);
        Assert.Equal("Blueprint/D5/S0/Carrier/Target.md", dependency.Dependency);
        Assert.Equal("Blueprint/D5/S0/Carrier/Source.md", dependency.Dependent);
        var narrative = Assert.Single(model.Documents.NarrativeReferenceEdges);
        Assert.Equal("Blueprint/D5/S0/Carrier/Source.md", narrative.Source);
        Assert.Equal("Blueprint/D5/S0/Carrier/Target.md", narrative.Target);
        var join = Assert.Single(model.Joins.TruthAnchors);
        Assert.Equal("Blueprint/D5/S0/Carrier/Source.md", join.DocumentRepoPath);
        Assert.Equal(declaration.Value, join.LeanDeclarationGid);
        Assert.Equal("D5/S0/Carrier/Target.lean", join.FormalTruthRepoPath);
        Assert.True(model.DeferredLayers.SequenceEqual(["digestion"]));

        var roundTrip = TruthGraphJsonReader.Read(TruthGraphJsonWriter.Write(model).AsSpan());
        Assert.True(model.Documents.Nodes.SequenceEqual(roundTrip.Documents.Nodes));
        Assert.True(model.Documents.DependencyEdges.SequenceEqual(roundTrip.Documents.DependencyEdges));
        Assert.True(model.Documents.NarrativeReferenceEdges.SequenceEqual(roundTrip.Documents.NarrativeReferenceEdges));
        Assert.True(model.Joins.TruthAnchors.SequenceEqual(roundTrip.Joins.TruthAnchors));
        Assert.True(model.DeferredLayers.SequenceEqual(roundTrip.DeferredLayers));
    }

    [Fact]
    public void ExportPreservesCoDeclarationDescribeIdentitiesAndCanonicalRoundTrip()
    {
        var declaration = LeanDeclarationRef.Create("D5/S0/Carrier/Target.anchor");
        var document = DocumentWithTwoDescribes("D5/S0/Carrier/Target", declaration);
        var reportFiles = new Dictionary<string, LeanFileReport>
        {
            ["D5/S0/Carrier/Target.lean"] = new([], [new LeanDeclaration(declaration.Value.Replace('/', '.'), "theorem", "True", [])]),
        };
        var report = LeanAxiomReport.Create(reportFiles);
        var catalog = DeclarationCatalog.Create(report);
        var projection = DocumentGraphExportProjection.Create(
            [new DocumentGraphDocument("Blueprint/D5/S0/Carrier/Target.md", document, "receipt-bound")],
            DocumentGraphAssembler.Assemble([document], catalog),
            catalog,
            new HashSet<string>(["D5/S0/Carrier/Target.lean"], StringComparer.Ordinal));
        var model = TruthGraphModelBuilder.Create(BuildFromFiles(
            new Dictionary<string, string> { ["D5/S0/Carrier/Target.lean"] = "theorem anchor : True := True.intro\n" },
            reportFiles), Provenance, projection);

        Assert.Equal(["first", "second"], model.Documents.DescribeNodes.Select(static node => node.DescribeId));
        Assert.Equal(["first", "second"], model.Joins.TruthAnchors.Select(static anchor => anchor.DescribeId));
        var bytes = TruthGraphJsonWriter.Write(model);
        Assert.True(bytes.AsSpan().SequenceEqual(TruthGraphJsonWriter.Write(TruthGraphJsonReader.Read(bytes.AsSpan())).AsSpan()));

        var danglingAnchor = model with
        {
            // Dangle exactly ONE anchor. Mutating both would give the two co-declaration
            // anchors an identical ordering key (DocumentRepoPath\0DescribeId\0LeanDeclarationGid),
            // so RequireStrictOrder would reject before the referential check ever runs and the
            // case would still pass with that check deleted. "first" < "missing" keeps the order
            // strictly ascending, leaving the dangling describe_id as the only reason to reject.
            Joins = new TruthGraphJoinsSection(model.Joins.TruthAnchors
                .Select(static (anchor, index) =>
                    index == 1 ? anchor with { DescribeId = "missing" } : anchor)
                .ToImmutableArray()),
        };
        Assert.Throws<FormatException>(() =>
            TruthGraphJsonReader.Read(TruthGraphJsonWriter.Write(danglingAnchor).AsSpan()));

        var otherDocument = new DocumentGraphNode(
            "Blueprint/D5/S0/Carrier/Other.md", "D5/S0/Carrier/Other", "receipt-free");
        var misboundDocument = model with
        {
            Documents = model.Documents with
            {
                Nodes = model.Documents.Nodes.Add(otherDocument)
                    .OrderBy(static node => node.RepoPath, StringComparer.Ordinal).ToImmutableArray(),
                DescribeNodes = model.Documents.DescribeNodes
                    .Select(static node => node with { DocumentGid = "D5/S0/Carrier/Other" })
                    .ToImmutableArray(),
            },
        };
        Assert.Throws<FormatException>(() =>
            TruthGraphJsonReader.Read(TruthGraphJsonWriter.Write(misboundDocument).AsSpan()));

        var retargetedDeclaration = model with
        {
            Documents = model.Documents with
            {
                DescribeNodes = model.Documents.DescribeNodes
                    .Select(static node => node with { LeanDeclarationGid = "D5/S0/Carrier/Target.other" })
                    .ToImmutableArray(),
            },
        };
        Assert.Throws<FormatException>(() =>
            TruthGraphJsonReader.Read(TruthGraphJsonWriter.Write(retargetedDeclaration).AsSpan()));
    }

    [Fact]
    public void DocumentProjectionRejectsMissingOrAmbiguousAnchorResolutionAndMissingFormalNode()
    {
        var reference = LeanDeclarationRef.Create("D5/S0/Carrier/Target.anchor");
        var document = Document("D5/S0/Carrier/Source", [DocumentEdge.TruthAnchor.Create(reference)]);
        var source = new DocumentGraphDocument("Blueprint/D5/S0/Carrier/Source.md", document, "receipt-free");

        Assert.Throws<InvalidOperationException>(() => DocumentGraphExportProjection.Create(
            [source],
            DocumentGraphAssembler.Assemble([document], null),
            DeclarationCatalog.Create(LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>())),
            new HashSet<string>(["D5/S0/Carrier/Target.lean"], StringComparer.Ordinal)));

        var ambiguous = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/S0/Carrier/Target.lean"] = new([], [
                new LeanDeclaration("anchor", "theorem", "True", []),
                new LeanDeclaration("Namespace.anchor", "theorem", "True", []),
            ]),
        });
        Assert.Throws<InvalidOperationException>(() => DocumentGraphExportProjection.Create(
            [source], DocumentGraphAssembler.Assemble([document], null),
            DeclarationCatalog.Create(ambiguous),
            new HashSet<string>(["D5/S0/Carrier/Target.lean"], StringComparer.Ordinal)));

        var resolved = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/S0/Carrier/Target.lean"] = new([], [new LeanDeclaration("anchor", "theorem", "True", [])]),
        });
        Assert.Throws<InvalidOperationException>(() => DocumentGraphExportProjection.Create(
            [source], DocumentGraphAssembler.Assemble([document], DeclarationCatalog.Create(resolved)),
            DeclarationCatalog.Create(resolved),
            new HashSet<string>(StringComparer.Ordinal)));
    }

    [Fact]
    public void StrictReaderRoundTripsEveryCapabilityField()
    {
        var dag = BuildFromFiles(
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
        var expected = TruthGraphModelBuilder.Create(dag, Provenance);

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
        var empty = BuildFromEntries(
            [new KeyValuePair<string, string>("Meta/only.txt", "one\n")],
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));
        var single = BuildFromEntries(
            [new KeyValuePair<string, string>("D5/S0/Carrier/Only.lean", "def only : Nat := 0\n")],
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                ["D5/S0/Carrier/Only.lean"] = Report(),
            });

        Assert.Empty(TruthGraphJsonReader.Read(TruthGraphJsonWriter.Write(TruthGraphModelBuilder.Create(empty, Provenance)).AsSpan()).Truth.Nodes);
        var node = Assert.Single(TruthGraphJsonReader.Read(TruthGraphJsonWriter.Write(TruthGraphModelBuilder.Create(single, Provenance)).AsSpan()).Truth.Nodes);
        Assert.Equal("D5.S0.Carrier.Only", node.ModuleName);
        Assert.Equal("closed", node.State);
        Assert.Equal(0, node.Depth);
    }

    [Theory]
    [InlineData("{}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-graph.v1\",\"schema_version\":1,\"provenance\":{},\"truth\":{},\"extra\":true}\n")]
    [InlineData("{\"schema\":\"wrong\",\"schema_version\":1,\"provenance\":{},\"truth\":{}}\n")]
    public void StrictReaderRejectsMalformedOrUnknownFields(string json) =>
        Assert.Throws<FormatException>(() => TruthGraphJsonReader.Read(Encoding.UTF8.GetBytes(json)));

    private static TruthDagProjection BuildFromEntries(
        IEnumerable<KeyValuePair<string, string>> files,
        IReadOnlyDictionary<string, LeanFileReport> reports) =>
        BuildFromFiles(files.ToDictionary(static pair => pair.Key, static pair => pair.Value, StringComparer.Ordinal), reports);

    private static TruthDagProjection BuildFromFiles(
        IReadOnlyDictionary<string, string> files,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
        return TruthDagProjectionAssembler.Build(snapshot, closure);
    }

    private static LeanFileReport Report(params string[] imports) =>
        new(imports.ToImmutableArray(), ImmutableArray<LeanDeclaration>.Empty);

    private static ScribeDocument Document(string gid, IEnumerable<DocumentEdge>? edges = null) =>
        ScribeDocument.Create(
            DocumentHeader.Create(
                GidRef.Create(gid),
                Generality.Instance,
                GidRef.Create("D5/B/" + gid["D5/".Length..]),
                new EvidenceMirror.Waiver(WaiverReason.Create("test-only")),
                [],
                Digest.Create("Test document.")),
            Heading.Create(gid),
            BlockSequence.Create([
                new DocumentBlock.Paragraph(InlineSequence.Create([
                    new Inline.Text(TextRun.Create("Body.")),
                ])),
            ]),
            edges ?? []);

    private static ScribeDocument DocumentWithTwoDescribes(string gid, LeanDeclarationRef declaration) =>
        ScribeDocument.Create(
            DocumentHeader.Create(GidRef.Create(gid), Generality.Instance,
                GidRef.Create("D5/B/" + gid["D5/".Length..]),
                new EvidenceMirror.Waiver(WaiverReason.Create("test-only")), [], Digest.Create("Test document.")),
            Heading.Create(gid),
            BlockSequence.Create([
                Describe.Lean(DescribeId.Create("first"), DeclarationHandle.Create(declaration.Value),
                    Heading.Create("First"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Body(), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("second"), DeclarationHandle.Create(declaration.Value),
                    Heading.Create("Second"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Body(), DescribeRole.Definition),
            ]));

    private static BlockSequence Body() => BlockSequence.Create([
        new DocumentBlock.Paragraph(InlineSequence.Create([new Inline.Text(TextRun.Create("Body."))])),
    ]);

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            files.Select(static file => RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;
}
