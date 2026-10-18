using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ExpandingNormProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/ExpandingNormProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Norm products from an expanding-factor lower bound.",
        H("Norm products from an expanding-factor lower bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zhangli-expandingnormproduct-sq-le-product-of-expanding-lower-bound"),
                DeclarationHandle.Create(Module + ".sq_le_product_of_expanding_lower_bound"),
                H("Balancing a common lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix complex square matrices A and B, a unitarily invariant norm N, and a nonnegative real m. If m≤N(ATB) for every expanding T, then for every invertible W, m²≤N(AWB)N(A(W⁻¹)*B). Apply the lower bound to Tₜ=(tW+t⁻¹(W⁻¹)*)/2. The triangle inequality gives 2m≤tN(AWB)+t⁻¹N(A(W⁻¹)*B) for every positive t, and scalar optimization gives the result, including zero factors. A and B need not be diagonal or positive."))),
                DescribeRole.Theorem))));
}
