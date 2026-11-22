using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9TwentyTwoCoverRefutationDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A twenty-two-triple obstruction to the singleton-mask argument",
        H("Pair and five-set coverage on nine axes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-twenty-two-cover-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("A proposed singleton-mask criterion at twenty-two triples"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proposed criterion asks whether twenty-two distinct triples on nine axes "
                    + "must singly cover some five-set whenever every pair and every five-set are covered."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("q9-twenty-two-cover-refutation"),
                DeclarationHandle.Create(Module + ".result"),
                H("A pair-covering family doubles every five-set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Lean checks that the displayed family has exactly twenty-two triples, that "
                        + "all 36 pairs extend to a triple, and that all 126 five-sets contain at least "
                        + "two triples. This refutes the proposed criterion.")),
                    Paragraph(Text(
                        "The witness concerns the necessary direction-cover conditions. Its realization "
                        + "as directions of a universally saturated component is a separate question. "
                        + "Hong, Wu and Xia ask whether f₂(Q₉) equals three or four. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover")),
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage"))
        ]));
}
