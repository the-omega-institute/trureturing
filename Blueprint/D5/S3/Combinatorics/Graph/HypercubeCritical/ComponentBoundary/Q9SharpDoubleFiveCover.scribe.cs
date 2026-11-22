using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SharpDoubleFiveCoverDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SharpDoubleFiveCover";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp eight-point double-cover bound and its Q9 application",
        H("Fourteen triples on eight points and singleton masks on nine axes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-sharp-double-five-cover-bound"),
                DeclarationHandle.Create(Module + ".fourteen_le_card_of_double_five_cover"),
                H("Double coverage on eight points requires fourteen triples"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If every five-set of an eight-point set contains at least two triples from "
                        + "a family of distinct triples, the family has at least fourteen members.")),
                    Paragraph(Text(
                        "The thirteen-triple lower bound reduces the proof to excluding equality "
                        + "at thirteen. Deletion counting and the Fano link bound cap every point "
                        + "degree at five. The degree sum then forces one point of degree four and "
                        + "seven of degree five. On those seven points, the pairs of codegree one "
                        + "form a triangle-free graph with at least eleven edges. Its parts have "
                        + "sizes four and three. Internal pairs require codegree at least two and "
                        + "crossing pairs require at least one. The codegree sum exceeds this "
                        + "baseline by one, so at most one pair exceeds its baseline. Each mixed "
                        + "triple on the seven points must contain that pair, which bounds the "
                        + "number of such triples by three. They can account for at most six crossing "
                        + "pairs, and the four triples through the degree-four point for at most four "
                        + "more. All twelve crossing pairs must occur."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-cyclic-double-five-cover-witness"),
                DeclarationHandle.Create(Module + ".exists_fourteen_triple_double_five_cover"),
                H("A cyclic family attains the bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the residues modulo seven, take the seven translates of {0, 1, 3}. "
                        + "Add the triples formed by adjoining the eighth point to each consecutive "
                        + "pair in the seven-cycle. Lean checks that the fourteen triples cover "
                        + "each of the 56 five-sets at least twice."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-singleton-five-mask-at-twenty-types"),
                DeclarationHandle.Create(Module + ".exists_singleton_five_mask_of_card_le_twenty"),
                H("At most twenty direction types force a singleton five-axis mask"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A family of at most twenty distinct triples on nine axes that covers "
                        + "every five-axis mask has a mask containing exactly one triple. If every "
                        + "mask were doubly covered, the nine eight-axis deletions would require "
                        + "at least 126 incidences. Each triple survives six deletions, for at most "
                        + "120 incidences.")),
                    Paragraph(Text(
                        "In a subcubic 258-vertex induced subgraph of Q9, take an actual component "
                        + "with universal Huang saturation. Use the distinct full direction sets "
                        + "at its degree-three vertices as the triple family. Singularity at every "
                        + "five-axis mask gives coverage by those triples. With at most twenty "
                        + "distinct types, the singleton mask gives a common full direction triple "
                        + "for every degree-three vertex whose directions lie in that mask. "
                        + "If the component is balanced, the same mask is singular and the "
                        + "masked-face theorem yields an eleven-vertex masked component with the "
                        + "three four-edge paths of its normal form. This is a conditional "
                        + "restriction for Hong, Wu and Xia's open Problem 2, which asks whether "
                        + "f₂(Q₉) is three or four. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SingletonFiveMask")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FanoDeletion")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SevenVertexBipartite")),
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation")),
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DirectionCoverage")),
            DocumentEdge.NarrativeReference.ToDocument(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedFiveFace"))
        ]));
}
