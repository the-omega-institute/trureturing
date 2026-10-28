using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldBalancedPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal balanced multiplier", H("The literal balanced multiplier"), Blocks(
            Describe.Lean(DescribeId.Create("threefieldbalancedpolynomial-balancedpolynomial"),
                DeclarationHandle.Create(Prefix + "balancedPolynomial"),
                H("The literal balanced multiplier"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the original order s,x,z the multiplier is (s+x)^a0 x^a1 z^a2 s^k (s+x-z)^k (x-z)^k."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threefieldbalancedpolynomial-balancedrotatedpolynomial"),
                DeclarationHandle.Create(Prefix + "balancedRotatedPolynomial"),
                H("The supported coefficient order"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reordering coefficient arguments as s,z,x gives (Z+X)^a0 Z^a1 Y^a2 X^k (X+Z-Y)^k (Z-Y)^k."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("threefieldbalancedpolynomial-balanced-action-rotate"),
                DeclarationHandle.Create(Prefix + "balanced_action_rotate"),
                H("Finite action and reordering"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite polynomial action commutes with swapping the second and third coefficient arguments. This is an identity of signed coefficient functions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("threefieldbalancedpolynomial-balanced-action-expansion"),
                DeclarationHandle.Create(Prefix + "balanced_action_expansion"),
                H("The exact finite clearing expansion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expanding the two difference factors gives j,l from zero through k. The remaining positive factor has exponent a0+k-j and is expanded by its finite binomial theorem. This gives the literal finite clearing used by the balanced canonical channel."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("threefieldbalancedpolynomial-balanced-injective"),
                DeclarationHandle.Create(Prefix + "balanced_injective"),
                H("Cancellation on the supported chamber"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial is injective on coefficient functions with a uniform first cutoff and a second cutoff at each fixed first exponent in s,z,x order. The X+Z factor uses the first cutoff. The X+Z-Y factor uses induction through first-coordinate rows and then the current row second cutoff. No x cutoff or domain assumption is required."))), DescribeRole.Theorem))));
}
