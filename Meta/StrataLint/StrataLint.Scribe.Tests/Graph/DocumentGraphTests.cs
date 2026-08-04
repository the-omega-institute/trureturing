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

        var result = DocumentGraphAssembler.Assemble([source], EmptyLeanReport());

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
            [dependencyA, dependencyB], EmptyLeanReport());
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
            [narrativeA, narrativeB], EmptyLeanReport()).Findings);
    }

    [Fact]
    public void ReferenceLinksAreDeterministicAndRoleOrdered()
    {
        var lean = LeanDeclarationRef.Create("D5/S0/Test/Target.anchor");
        var target = Document("D5/S0/Test/Target");
        var source = Document(
            "D5/S0/Test/Source",
            [
                DocumentEdge.NarrativeReference.ToDescribe(
                    GidRef.Create("D5/S0/Test/Target"), DescribeId.Create("target")),
                DocumentEdge.TruthAnchor.Create(lean),
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Test/Target")),
            ]);
        var report = LeanReport(lean);
        var graph = DocumentGraphAssembler.Assemble([source, target], report);
        Assert.Empty(graph.Findings);

        var first = CanonicalMarkdownWriter.Write(source, report, graph: graph);
        var second = CanonicalMarkdownWriter.Write(source, report, graph: graph);
        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        var markdown = Encoding.UTF8.GetString(first.AsSpan());
        var targetMarkdown = Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(target, report, graph: graph).AsSpan());
        var truthIndex = markdown.IndexOf(
            "- Truth anchor: `D5/S0/Test/Target.anchor`", StringComparison.Ordinal);
        var dependencyIndex = markdown.IndexOf(
            "- Dependency: [D5/S0/Test/Target](Target.md)", StringComparison.Ordinal);
        var narrativeIndex = markdown.IndexOf(
            "- Narrative reference: [D5/S0/Test/Target#describe/target](Target.md#describe-target)",
            StringComparison.Ordinal);
        Assert.Contains("## References", markdown, StringComparison.Ordinal);
        Assert.Contains("<a id=\"describe-target\"></a>", targetMarkdown, StringComparison.Ordinal);
        Assert.True(
            truthIndex >= 0 && truthIndex < dependencyIndex && dependencyIndex < narrativeIndex,
            $"indices={truthIndex},{dependencyIndex},{narrativeIndex}\n{markdown}");
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
                DocumentBlock.Describe.Remark(
                    DescribeId.Create("target"),
                    Heading.Create("Target"),
                    DescribeStatement.FromFormula(new Formula.Number(1)),
                    DescribeProvenance.RepoDerived(),
                    BlockSequence.Create([
                        new DocumentBlock.Paragraph(InlineSequence.Create([
                            new Inline.Text(TextRun.Create("Body.")),
                        ])),
                    ])),
            ]),
            edges ?? []);

    private static LeanAxiomReport EmptyLeanReport() =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());

    private static LeanAxiomReport LeanReport(LeanDeclarationRef reference) =>
        LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [reference.Reference.Path.Value] = new(
                [],
                [new LeanDeclaration(
                    reference.Value,
                    "theorem",
                    "True",
                    ["propext", "Quot.sound", "Classical.choice"])])
        });
}
