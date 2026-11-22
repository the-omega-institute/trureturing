using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CircuitPassiveCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CircuitPassiveCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alternating-form equations separated by the indices with zero weight.",
        H("Circuit Coordinates with Zero Weights"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("insertion-project"),
                DeclarationHandle.Create(Module + ".insertion_project"),
                H("Weighted insertion preserves the intersection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose a set of basis indices whose weights vanish. Keeping the coefficients "
                    + "with one prescribed intersection with that set commutes with insertion of "
                    + "the weighted vector. Only indices outside the chosen set can contribute "
                    + "to the insertion sum, so each contributing face has the same intersection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-split"),
                DeclarationHandle.Create(Module + ".exists_split"),
                H("Product decomposition of the weighted kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For forms killed by both weighted insertion and a fixed integer, the "
                    + "projections give a linear equivalence with the product of the parts "
                    + "supported on each prescribed intersection. Adding the projected forms "
                    + "recovers the original form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("split-with-omitted-faces"),
                DeclarationHandle.Create(Module + ".split_with_omitted_faces"),
                H("Omitted faces constrain individual factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Requiring the coefficient of an omitted face to vanish restricts the "
                    + "factor indexed by its intersection with the zero-weight set. Omitted "
                    + "faces with distinct intersections therefore impose equations in "
                    + "different factors of the product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-restrictions-product"),
                DeclarationHandle.Create(Module + ".independent_restrictions_product"),
                H("Restrictions on distinct product factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each coordinate at least one of the two restrictions is the whole module. Reordering the "
                    + "two entries at the coordinates where necessary identifies the unrestricted times doubly "
                    + "restricted product with the product of the individually restricted families."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("separated-coefficients-product"),
                DeclarationHandle.Create(Module + ".separated_coefficients_product"),
                H("Product identity for two separated coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose the submodule of alternating forms is preserved by the projections to fixed "
                    + "intersections with a chosen set of indices. Two coefficients with distinct intersections "
                    + "restrict different factors. The unrestricted times doubly restricted forms are equivalent "
                    + "to the product of the two single restrictions."))),
                DescribeRole.Theorem))));
}
