using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class DocumentGraphTests
{
    [Fact]
    public void EdgeRolesHaveTypedTargetsAndAClosedHierarchy()
    {
        Assert.True(typeof(DocumentEdge).IsAbstract);
        Assert.All(
            typeof(DocumentEdge).GetConstructors(
                System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic),
            static constructor => Assert.True(
                constructor.IsPrivate || constructor.IsFamilyAndAssembly));
        Assert.Equal(
            [typeof(DocumentEdge.Dependency), typeof(DocumentEdge.NarrativeReference), typeof(DocumentEdge.TruthAnchor)],
            typeof(DocumentEdge).GetNestedTypes().OrderBy(static type => type.Name).ToArray());

        var truth = DocumentEdge.TruthAnchor.Create(LeanDeclarationRef.Create("D5/S0/Test/Target.alpha"));
        var dependency = DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Test/Target"));
        var narrative = DocumentEdge.NarrativeReference.ToDescribe(
            GidRef.Create("D5/S0/Test/Target"),
            DescribeId.Create("alpha"));

        Assert.IsType<LeanDeclarationRef>(truth.Target);
        Assert.IsType<GidRef>(dependency.Target);
        Assert.IsType<NarrativeTarget.Describe>(narrative.Target);
        Assert.Throws<ArgumentException>(() =>
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Test/Target.alpha")));
        Assert.Throws<ArgumentException>(() =>
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S0/Test/Target.alpha")));
    }

    [Fact]
    public void AssemblerFailsClosedForDanglingTargets()
    {
        var source = Document(
            "D5/S0/Test/Source",
            [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Test/Missing"))]);

        var result = DocumentGraphAssembler.Assemble([source], EmptyCatalog());

        var finding = Assert.Single(result.Findings);
        Assert.Equal("dangling-document-edge", finding.Code);
        Assert.Contains("D5/S0/Test/Missing", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DependencyCyclesFailWithPathButNarrativeCyclesAreAllowed()
    {
        var dependencyA = Document(
            "D5/S0/Test/A",
            [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Test/B"))]);
        var dependencyB = Document(
            "D5/S0/Test/B",
            [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Test/A"))]);

        var dependencyResult = DocumentGraphAssembler.Assemble(
            [dependencyA, dependencyB], EmptyCatalog());
        var cycle = Assert.Single(dependencyResult.Findings);
        Assert.Equal("dependency-cycle", cycle.Code);
        Assert.Contains("D5/S0/Test/A -> D5/S0/Test/B -> D5/S0/Test/A", cycle.Message, StringComparison.Ordinal);

        var narrativeA = Document(
            "D5/S0/Test/A",
            [DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S0/Test/B"))]);
        var narrativeB = Document(
            "D5/S0/Test/B",
            [DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S0/Test/A"))]);

        Assert.Empty(DocumentGraphAssembler.Assemble(
            [narrativeA, narrativeB], EmptyCatalog()).Findings);
    }

    [Fact]
    public void ReferenceLinksHaveCanonicalBytesAcrossOrderingAndGraphContext()
    {
        var lean = LeanDeclarationRef.Create("D5/S0/Test/Target.anchor");
        var target = Document("D5/S0/Test/Target");
        var auxiliary = Document("D5/S0/Test/Auxiliary");
        var source = Document(
            "D5/S0/Test/Source",
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Test/Target")),
                DocumentEdge.NarrativeReference.ToDescribe(
                    GidRef.Create("D5/S0/Test/Target"), DescribeId.Create("target")),
                DocumentEdge.TruthAnchor.Create(lean),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Test/Auxiliary")),
            ]);
        var report = LeanReport(lean);
        var catalog = DeclarationCatalog.Create(report);
        var graph = DocumentGraphAssembler.Assemble([source, target, auxiliary], catalog);
        Assert.Empty(graph.Findings);

        var first = CanonicalMarkdownWriter.Write(source, catalog, graph: graph);
        var second = CanonicalMarkdownWriter.Write(source, catalog, graph: graph);
        var expectedSource = Encoding.UTF8.GetBytes(
            "# D5/S0/Test/Source\n\n"
            + "## Abstract\n\n"
            + "Test document.\n\n"
            + "**Remark 1.1 (Target).**\n\n"
            + "$$\n1\n$$\n\n"
            + "*Source.* Repository-derived.\n\n"
            + "*Commentary.*\n\n"
            + "Body.\n\n"
            + "## References\n\n"
            + "- Truth anchor: `D5/S0/Test/Target.anchor`\n"
            + "- Dependency: [D5/S0/Test/Auxiliary](Auxiliary.md)\n"
            + "- Dependency: [D5/S0/Test/Target](Target.md)\n"
            + "- Narrative reference: [D5/S0/Test/Target#describe/target](Target.md#describe-target)\n");
        var expectedTarget = Encoding.UTF8.GetBytes(
            "# D5/S0/Test/Target\n\n"
            + "## Abstract\n\n"
            + "Test document.\n\n"
            + "<a id=\"describe-target\"></a>\n\n"
            + "**Remark 1.1 (Target).**\n\n"
            + "$$\n1\n$$\n\n"
            + "*Source.* Repository-derived.\n\n"
            + "*Commentary.*\n\n"
            + "Body.\n");

        Assert.Equal(expectedSource, first.ToArray());
        Assert.Equal(expectedSource, second.ToArray());
        Assert.Equal(
            expectedTarget,
            CanonicalMarkdownWriter.Write(target, catalog, graph: graph).ToArray());
    }

    [Fact]
    public void ReceiptFreeDocumentsProjectDirectLeanImportsAsDependencies()
    {
        var source = Document("D5/S0/Test/Source");
        var target = Document("D5/S0/Test/Target");
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/S0/Test/Source.lean"] = new(["D5.S0.Test.Target"], []),
            ["D5/S0/Test/Target.lean"] = new([], []),
        });

        var graph = DocumentGraphAssembler.Assemble(
            [source, target],
            DeclarationCatalog.Create(report),
            autoWireDocumentGids: new HashSet<string>(StringComparer.Ordinal)
            {
                source.Header.Gid.Value,
            });

        Assert.Empty(graph.Findings);
        var dependency = Assert.Single(graph.For(source).OfType<DocumentEdge.Dependency>());
        Assert.Equal(target.Header.Gid.Value, dependency.Target.Value);
        var markdown = Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(
                source, DeclarationCatalog.Create(report), graph: graph).AsSpan());
        Assert.Contains(
            "- Dependency: [D5/S0/Test/Target](Target.md)",
            markdown,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ReceiptBoundDocumentsStillCarryImplicitDescribeTruthAnchors()
    {
        var source = DocumentWithLeanAnchor(
            "D5/S0/Test/Source",
            "D5/S0/Test/Source.anchor");
        var report = LeanReport(LeanDeclarationRef.Create("D5/S0/Test/Source.anchor"));

        var graph = DocumentGraphAssembler.Assemble(
            [source],
            DeclarationCatalog.Create(report),
            autoWireDocumentGids: new HashSet<string>(StringComparer.Ordinal));

        var anchor = Assert.Single(graph.For(source).OfType<DocumentEdge.TruthAnchor>());
        Assert.Equal("anchor", anchor.DescribeId?.Value);
    }

    [Fact]
    public void AssemblerResolvesShortNameWhenNamespaceDiffersFromModulePath()
    {
        var source = DocumentWithLeanAnchor(
            "D5/S0/Test/Source",
            "D5/S0/Test/Source.anchor");
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/S0/Test/Source.lean"] = new(
                [],
                [new LeanDeclaration(
                    "Other.Namespace.anchor",
                    "theorem",
                    "True",
                    ["propext", "Quot.sound", "Classical.choice"])])
        });

        var graph = DocumentGraphAssembler.Assemble([source], DeclarationCatalog.Create(report));

        Assert.Empty(graph.Findings);
        var anchor = Assert.Single(graph.For(source).OfType<DocumentEdge.TruthAnchor>());
        Assert.Equal("D5/S0/Test/Source.anchor", anchor.Target.Value);
    }

    [Fact]
    public void ReceiptBoundDocumentsFilterSelfNarrativeReferences()
    {
        var source = Document(
            "D5/S0/Test/Source",
            [DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S0/Test/Source"))]);

        var graph = DocumentGraphAssembler.Assemble(
            [source],
            EmptyCatalog(),
            autoWireDocumentGids: new HashSet<string>(StringComparer.Ordinal));

        Assert.Empty(graph.For(source).OfType<DocumentEdge.NarrativeReference>());
    }

    [Fact]
    public void DefaultAssemblyFiltersSelfNarrativeReferences()
    {
        var source = Document(
            "D5/S0/Test/Source",
            [DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S0/Test/Source"))]);

        var graph = DocumentGraphAssembler.Assemble(
            [source],
            EmptyCatalog(),
            autoWireDocumentGids: null);

        Assert.Empty(graph.For(source).OfType<DocumentEdge.NarrativeReference>());
    }

    [Fact]
    public void ReceiptBoundDocumentsPreserveNarrativeReferencesToOtherDocuments()
    {
        var source = Document(
            "D5/S0/Test/Source",
            [DocumentEdge.NarrativeReference.ToDocument(GidRef.Create("D5/S0/Test/Target"))]);
        var target = Document("D5/S0/Test/Target");

        var graph = DocumentGraphAssembler.Assemble(
            [source, target],
            EmptyCatalog(),
            autoWireDocumentGids: new HashSet<string>(StringComparer.Ordinal));

        var narrative = Assert.Single(graph.For(source).OfType<DocumentEdge.NarrativeReference>());
        var documentTarget = Assert.IsType<NarrativeTarget.Document>(narrative.Target);
        Assert.Equal(target.Header.Gid.Value, documentTarget.DocumentGid.Value);
    }

    [Fact]
    public void ReceiptBoundDocumentsPreserveSelfDescribeNarrativeReferences()
    {
        var source = Document(
            "D5/S0/Test/Source",
            [DocumentEdge.NarrativeReference.ToDescribe(
                GidRef.Create("D5/S0/Test/Source"),
                DescribeId.Create("target"))]);

        var graph = DocumentGraphAssembler.Assemble(
            [source],
            EmptyCatalog(),
            autoWireDocumentGids: new HashSet<string>(StringComparer.Ordinal));

        var narrative = Assert.Single(graph.For(source).OfType<DocumentEdge.NarrativeReference>());
        var describeTarget = Assert.IsType<NarrativeTarget.Describe>(narrative.Target);
        Assert.Equal(source.Header.Gid.Value, describeTarget.DocumentGid.Value);
        Assert.Equal("target", describeTarget.DescribeId.Value);
    }

    [Fact]
    public void CoDeclarationDescribesRemainDistinct()
    {
        var declaration = LeanDeclarationRef.Create("D5/S0/Test/Source.anchor");
        var source = DocumentWithTwoLeanAnchors("D5/S0/Test/Source", declaration);
        var graph = DocumentGraphAssembler.Assemble(
            [source], DeclarationCatalog.Create(LeanReport(declaration)));

        var anchors = graph.For(source).OfType<DocumentEdge.TruthAnchor>().ToArray();
        Assert.Equal(2, anchors.Length);
        Assert.Equal(["first", "second"], anchors.Select(anchor => anchor.DescribeId!.Value));
    }

    private static ScribeDocument Document(
        string gid,
        IEnumerable<DocumentEdge>? edges = null) =>
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
                Describe.Remark(
                    DescribeId.Create("target"),
                    Heading.Create("Target"),
                    new Formula.Number(1),
                    AssessedProvenance.FromRepo(),
                    BlockSequence.Create([
                        new DocumentBlock.Paragraph(InlineSequence.Create([
                            new Inline.Text(TextRun.Create("Body.")),
                        ])),
                    ])),
            ]),
            edges ?? []);

    private static DeclarationCatalog EmptyCatalog() => DeclarationCatalog.Create(
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()));

    private static ScribeDocument DocumentWithLeanAnchor(string gid, string declaration) =>
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
                Describe.Lean(
                    DescribeId.Create("anchor"),
                    DeclarationHandle.Create(declaration),
                    Heading.Create("Anchor"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    BlockSequence.Create([
                        new DocumentBlock.Paragraph(InlineSequence.Create([
                            new Inline.Text(TextRun.Create("Body.")),
                        ])),
                    ]),
                    DescribeRole.Definition),
            ]));

    private static ScribeDocument DocumentWithTwoLeanAnchors(string gid, LeanDeclarationRef declaration) =>
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

    private static LeanAxiomReport LeanReport(LeanDeclarationRef reference) =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [reference.Reference.Path.Value] = new(
                [],
                [new LeanDeclaration(
                    reference.Value.Replace('/', '.'),
                    "theorem",
                    "True",
                    ["propext", "Quot.sound", "Classical.choice"])])
        });
}
