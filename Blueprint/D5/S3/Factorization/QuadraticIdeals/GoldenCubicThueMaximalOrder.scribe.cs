using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicThueMaximalOrderDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The marked cubic admits an explicit maximal integral lattice and signed field discriminant 81P squared.",
        H("Maximal order and field discriminant of the native Thue cubic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-maximal-span"),
                DeclarationHandle.Create(Module + "native_maximal_span"),
                H("The four marked generators span the full integral closure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The scaled root basis has trace determinant 81P to the fourth. Add the monic companion and use its two Eisenstein certificates to cancel the only denominator primes globally. The result is an equality of actual integer submodules, not a polynomial discriminant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-field-discriminant"),
                DeclarationHandle.Create(Module + "native_field_discriminant"),
                H("The exact signed field discriminant is 81P squared"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take the third integral generator to be (beta + k alpha + l)/P with A k congruent to D and A l congruent to D squared modulo P. The same lattice is obtained for every such pair. Its trace determinant is the signed number-field discriminant. This does not by itself exclude the original two-prime factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-thue-actual-factorization-field-discriminant"),
                DeclarationHandle.Create(Module + "actual_factorization_field_discriminant"),
                H("The original Lucas factorization supplies the marked field and its integral basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original Lucas block equation itself supplies the oriented square-role ideal, "
                    + "the actual Thue splitting field, and all unit conditions. Its field discriminant "
                    + "is 81P squared, and the explicit three vectors span its integral closure. "
                    + "The original nonexistence claim is still open."))),
                DescribeRole.Theorem))));
}
