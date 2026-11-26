using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent;

internal sealed class Q9LaurentSharedCutBoxesDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/";
    private const string Owner = Boundary + "Q9LaurentSharedCutBoxes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A family of balanced transverse cut boxes connected by overlaps has a common center and a single unordered cut if the boxes share an integer height with the stated offset law and each occupied point has odd multiplicity.",
        H("Rigidity of transverse cut boxes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-balanced-cut-centers"),
                DeclarationHandle.Create(Owner + "center_eq_of_overlap"),
                H("Integer height determines the common center"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translate one shared point to zero by symmetric difference. Each relative center then consists of two crossing axes. If the centers differ, the crossing pairs can be rearranged to produce another shared point that changes an axis on which the centers disagree. The two height differences on that axis have opposite signs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-shared-cut-odd-fibers"),
                DeclarationHandle.Create(Owner + "same_cut_of_connected_odd_box_fibers"),
                H("Odd incidence determines the unordered cut"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the cut boxes are balanced and any two are linked by a chain of overlaps, all boxes share an integer height with the stated offset law, and each occupied point lies in an odd number of boxes. The overlap chains propagate a common center throughout the family. The Hamming distance between the cut membership signatures of two axes counts the boxes containing the corresponding translated pair. Distinct signatures therefore have opposite parity, which forces all nonconstant cuts to separate the same pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-shared-cut-actual-stars"),
                DeclarationHandle.Create(Owner + "same_cut_of_realized_common_star_boxes"),
                H("Common stars give odd fibers in the quotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the common-star cover induces a connected subgraph of the nine-dimensional cube and the encoded projection of each transverse component is exactly the point set of its balanced cut box. The boxes share an integer height with the stated offset law, and each two-step move between side vertices stays in its component or preserves the projection. These moves connect the family of boxes by overlaps. Each occupied point then lies in exactly three boxes indexed by distinct transverse components. The three leaves of a common star differ in the deleted coordinates, which are fixed within a component. This supplies the odd incidence needed to treat the common-block branch of the Laurent approach to Hong, Wu and Xia’s Problem 2."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9LaurentTransverseFibers"))]));
}
