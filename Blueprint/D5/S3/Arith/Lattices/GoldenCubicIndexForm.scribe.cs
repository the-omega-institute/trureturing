using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class GoldenCubicIndexFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden cubic coordinate order has an exact trace discriminant and index form.",
        H("Golden Cubic Order Discriminant and Index Form"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-discriminant-index-form"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/GoldenCubicIndexForm.golden_cubic_discriminant_index_form"),
                H("Trace discriminant and power-basis determinant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the actual Lucas block B_j = L_(3^j)^2 + 3, write "
                    + "a_j = (B_j - 1)/9. The integral coordinate ring on "
                    + "(1, theta, beta) uses the cubic multiplication table. "
                    + "The determinant of its regular-trace Gram matrix is "
                    + "-3 B_j^2. For alpha = r + b theta + c beta, the signed "
                    + "determinant of (1, alpha, alpha^2) is "
                    + "3b^3 + 3b^2c + bc^2 - a_j c^3, and nine times this "
                    + "determinant is (3b+c)^3 - B_j c^3. "
                    + "The theorem concerns this constructed coordinate order; "
                    + "its embedding in the cubic number field and the maximal "
                    + "order index remain separate obligations."))),
                DescribeRole.Theorem))));
}
