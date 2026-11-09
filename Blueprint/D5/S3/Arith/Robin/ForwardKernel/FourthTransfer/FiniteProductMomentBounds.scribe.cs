using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.FourthTransfer;

internal sealed class FiniteProductMomentBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FiniteProductMomentBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth moments control products of at most four factors and their replacement errors.",
        H("Finite product moment bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("product-integrable"),
                DeclarationHandle.Create(Prefix + "product_integrable"),
                H("Integrability of finite products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive k on any measure space, if each of k real functions belongs to Lk, their product is integrable. The reciprocal Holder exponents sum to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-fourth-bound"),
                DeclarationHandle.Create(Prefix + "product_fourth_bound"),
                H("Products controlled by fourth moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On any probability space, let 1<=k<=4 and let f_i belong to L4. If the fourth moment of f_i is at most C_i>=0, then the integral of the absolute product is at most the product of C_i^(1/4). Holder at exponent k and monotonicity of probability-space Lp norms give the estimate, including when a bound vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-fourth-difference-bound"),
                DeclarationHandle.Create(Prefix + "product_fourth_difference_bound"),
                H("Fourth moment control of replacement errors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a probability space with 1<=k<=4, suppose both families have fourth moments at most K>=0 and their differences have fourth moments at most D>=0. The L1 distance between the products is at most k*D^(1/4)*K^((k-1)/4). The proof permits K=0 and D=0 and uses the real-power convention K^0=1 when k=1."))),
                DescribeRole.Theorem))));
}
