using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class PrimeContactCubeLiftDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "PrimeContactCubeLift";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer lift of the entire signed cube contact neighborhood",
        H("The integer lift of the entire signed cube contact neighborhood"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cube-prime-two-common-rows"),
                DeclarationHandle.Create(Module + ".common_rows_of_hammingDist_two"),
                H("Two distance-two columns have one occupied and one empty common row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signed products around a Huang square are negative. "
                    + "Coherence at occupied rows rules out two occupied corners. "
                    + "Cancellation with the unit kernel signs rules out two empty corners. "
                    + "The common neighboring rows therefore have opposite classifications."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-prime-full-row-exponents"),
                DeclarationHandle.Create(Module + ".exists_row_exponent"),
                H("Integer transport extends to every neighboring row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an empty row the two adjacent column exponents agree after adding "
                    + "their respective coordinate basis vectors. The other corner of "
                    + "the square is occupied, where subtracting those basis vectors "
                    + "gives the same lower exponent. This extends the potential to all "
                    + "contact rows regardless of their occupied contact multiplicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-prime-signs-agree"),
                DeclarationHandle.Create(Module + ".sign_product_eq_of_reachable"),
                H("Kernel signs and switching signs agree up to a component sign"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The occupied and empty equations on a mixed square identify the "
                    + "products of the switching and kernel signs on its two columns. "
                    + "Their ratio is therefore constant along an empty-row path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cube-prime-grade-and-parity"),
                DeclarationHandle.Create(Module + ".grade_and_parity_of_connected"),
                H("The integer potential preserves the grade and shifted binary coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The gain along an empty contact edge is a difference of two "
                        + "coordinate basis vectors. It preserves the integer coordinate sum. "
                        + "Reducing each coordinate modulo two gives the corresponding "
                        + "cube bit after one global bit translation.")),
                    Paragraph(Text(
                        "For the two-contact paired-fibre branch of Hong, Wu and Xia's "
                        + "Problem 2, this makes the prime transport a lattice lift of "
                        + "the actual cube neighborhood. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "PrimeContactTransport")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance"))
        ]));
}
