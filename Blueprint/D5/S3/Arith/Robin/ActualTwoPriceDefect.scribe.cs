using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualTwoPriceDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ActualTwoPriceDefect.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete original prime-layer optimizers and their two-price pressure identity.",
        H("Actual optimizers and two-price defects"),
        Blocks(
            Paragraph(Text("The objective is log(sigma(n)/n)-q*log(n). The strict integer selects every layer with marginal greater than q; the maximal integer also includes every equality layer. All primes, positive layers and simultaneous ties are retained.")),
            Describe.Lean(
                DescribeId.Create("actual-maximal-integer-specification"),
                DeclarationHandle.Create(Prefix + "maximalInteger_spec"),
                H("The complete maximal optimizer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive real price, the weak layer set is finite and each prime fiber is a complete initial interval. Its finite exponent product is positive, has the stated exponents, and is the greatest original optimizer in the stated order. Finiteness and optimality follow from the existing marginal decay and local threshold suppliers, without a finite prime or exponent truncation hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-pressure-integral"),
                DeclarationHandle.Create(Prefix + "pressure_integral"),
                H("Pressure across all activation events"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a,b>1, the oriented integral of clock(u)*weight(u) is pressure(price(b))-pressure(price(a)). Here price(u)=1/(u*log(u)), weight(u)=(1+log(u))/(u^2*log(u)^2), and clock(u) is the logarithm of the same strict optimizing integer. Compact layer support proves stability on the correct side of a tie. The one-sided derivative and integrability are proved before the fundamental theorem of calculus is applied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-oriented-identity"),
                DeclarationHandle.Create(Prefix + "two_price_oriented"),
                H("Keep the source integer at both prices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For x,a>1, the actual defect of integerAt(x) at price(a) equals the oriented integral from x to a of (clock(u)-clock(x))*weight(u). The source integer is retained rather than replaced by an independently chosen inventory."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-npc5-any-comparison-optimizer"),
                DeclarationHandle.Create(Prefix + "npc5_any_comparison_optimizer"),
                H("The same cost for every comparison optimizer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When A=clock(x)>1, every positive original optimizer at price(A), including the maximal tied optimizer, has objective gain over integerAt(x) equal to the integral from min(x,A) to max(x,A) of |clock(u)-clock(x)|*weight(u). Clock monotonicity pays both price orders. This exact defect identity does not supply the strict Robin endpoint sign."))),
                DescribeRole.Theorem))));
}
