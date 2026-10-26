using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class FourFieldMiddlePolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite middle spectator clearing", H("Finite middle spectator clearing"), Blocks(
            Describe.Lean(DescribeId.Create("fourfieldmiddlepolynomial-middle-action-expansion"),
                DeclarationHandle.Create(Prefix + "middle_action_expansion"),
                H("Literal middle multiplier"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any complex module and arbitrary signed four-variable distribution F in coordinates x,b,z,y, finite polynomial action by x^a0 (b+z)^a1 z^a2 y^a3 (x-b-z)^k (x-z)^k (x-y)^k b^k (b+z-y)^k (z-y)^k equals the explicit middle clearing. Three finite spectator indices p,r,s produce outer exponent e0-a0-3k+p+r+s and balanced bounds a1+p,a2+r,a3+s. Two further finite indices j,l expand the remaining cross factors, followed by the finite positive binomial expansion of b+z. All exponents may be signed. No substitution on a raw distribution or support assumption is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourfieldmiddlepolynomial-clearing-four-middle"),
                DeclarationHandle.Create(Prefix + "clearing_four_middle"),
                H("Original six pair factors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original four-field clearing factors into the v,t pair factor and five other pair factors. Their finite convolution evaluates F at x-3k+p+r+s, V-p-k+j, T-r-k+l, y-s-j-l with five signed binomial weights. Clearing the active V,T pair after this convolution equals the original six-pair polynomial action with all four labels fixed. This identity is used on actual canonical products."))), DescribeRole.Theorem))));
}
