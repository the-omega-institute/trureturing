using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class PrimeContactCardinalityGapDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "PrimeContactCardinalityGap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first cardinality gap of signed two-contact columns",
        H("The first cardinality gap of signed two-contact columns"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-contact-common-neighbor-bound"),
                DeclarationHandle.Create(Module + ".card_commonColumns_of_nonadj_le_two"),
                H("Nonadjacent columns share at most two distance-two neighbors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two nonadjacent columns with a common neighbor differ on four "
                    + "axes. The six possible intermediate labels form the octahedron "
                    + "graph on two-element subsets. Three intermediate columns would "
                    + "give a neighborhood vertex adjacent to two others, incompatible "
                    + "with the disjoint pairs arising from occupied partners."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-contact-column-count-gap"),
                DeclarationHandle.Create(Module + ".cardinality_gap_of_twoContact"),
                H("At least nine columns and no ten-column case"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The induced distance-two graph is four-regular. Counting "
                        + "two-step paths gives a lower bound of eleven minus the "
                        + "number of three-contact occupied rows at each column. This "
                        + "number is at most two, so the column count is at least nine.")),
                    Paragraph(Text(
                        "At ten columns the permutation-cover inequality and triangle "
                        + "incidence force eight columns incident to two triangles. "
                        + "Removing triangle edges would leave a simple two-regular "
                        + "graph on the remaining two vertices, a contradiction. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "PrimeContactCubeOrders"))]));
}
