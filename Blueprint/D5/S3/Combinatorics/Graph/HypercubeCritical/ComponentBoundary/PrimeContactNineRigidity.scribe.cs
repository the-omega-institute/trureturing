using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class PrimeContactNineRigidityDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "PrimeContactNineRigidity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nine-column equality and its cube grid",
        H("Nine-column equality and its cube grid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nine-two-contact-grid"),
                DeclarationHandle.Create(Module + ".eq_nineGrid_of_twoContact"),
                H("Nine columns are exactly a grid from two disjoint three-axis sets"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality in the two-step count forces two occupied partner "
                    + "pairs at the root. The two triples of their axes are disjoint. "
                    + "Each choice of one neighbor from each pair has a unique "
                    + "nonadjacent rectangle completion, yielding all nine vertices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nine-cube-center-rigidity"),
                DeclarationHandle.Create(Module + ".nine_column_equality"),
                H("The actual empty directions and occupied center are determined"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The signed square equations determine the empty directions "
                        + "as the other two axes of each triple. Thus the occupied "
                        + "center is constant across the grid. Hamming distance is "
                        + "twice the number of changed grid factors.")),
                    Paragraph(Text(
                        "For the paired-fibre branch of Hong, Wu and Xia's Problem 2, "
                        + "the nine-column case belongs to the rigid common-center "
                        + "shell geometry. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "PrimeContactCardinalityGap"))]));
}
