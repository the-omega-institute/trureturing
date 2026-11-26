using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.HilbertSmith;

internal sealed class CauchyDeterminantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/HilbertSmith/CauchyDeterminant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant of a matrix of reciprocals of pairwise sums factors into two ordered difference products.",
        H("The Cauchy determinant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("det-cauchy-matrix"),
                DeclarationHandle.Create(Prefix + "det_cauchyMatrix"),
                H("Cauchy determinant product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/HilbertOperators/krattenthaler1999determinant")),
                Blocks(
                    Paragraph(Text(
                        "Let x and y be ordered arrays of the same finite length over a field. "
                        + "Suppose every sum x(i)+y(j) is nonzero. The determinant of the matrix "
                        + "with entries 1/(x(i)+y(j)) is the product of x(j)-x(i) over i<j "
                        + "times the product of y(j)-y(i) over i<j, divided by the product of "
                        + "x(i)+y(j) over all ordered row and column pairs. Empty products equal "
                        + "one, and repeated coordinates are allowed.")),
                    Paragraph(Text(
                        "In positive dimension, eliminate the first column using its nonzero pivot. The remaining "
                        + "Schur complement is the smaller Cauchy matrix with each row and "
                        + "column scaled by its difference from the first coordinate divided "
                        + "by its sum with the first coordinate on the opposite side. Multiplying "
                        + "the scales, the pivot and the smaller determinant gives the products "
                        + "in the formula."))),
                DescribeRole.Theorem))));
}
