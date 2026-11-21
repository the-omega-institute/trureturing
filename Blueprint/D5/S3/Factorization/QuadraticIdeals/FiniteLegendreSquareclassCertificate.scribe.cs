using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class FiniteLegendreSquareclassCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/FiniteLegendreSquareclassCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Certificates of rational squareclass independence by actual finite Legendre signs.",
        H("Binary Legendre squareclass certificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-legendre-injective-squareclass"),
                DeclarationHandle.Create(Module + "not_isSquare_product_of_injective"),
                H("Injective Legendre sign columns rule out every nonempty rational-square product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A rational square of an integer is an integer square. After reducing at auxiliary primes its product sign is positive, so the selected subset would give a nonzero binary kernel vector."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-legendre-rational-squareclass"),
                DeclarationHandle.Create(Module + "not_isSquare_rational_product_of_injective"),
                H("The certificate works directly for rational squareclasses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplying each input by the square of its denominator preserves the tested squareclass and gives an integer Legendre input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-legendre-checkable-left-inverse"),
                DeclarationHandle.Create(Module + "injective_mulVec_of_left_inverse"),
                H("A binary matrix left inverse certifies injectivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite left inverse checked by matrix multiplication makes the sign oracle an independently verifiable certificate."))),
                DescribeRole.Theorem))));
}
