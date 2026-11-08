using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class BrownianFourthKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/BrownianFourthKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth Brownian pairing integral and strict dyadic excess kurtosis.",
        H("Brownian pairings and kurtosis"),
        Blocks(
            Paragraph(Text(
                "Let g be a real measurable integrable profile on the unit interval. "
                + "Its quadratic energy Q(g) is the double integral of g(s)g(t)min(s,t). "
                + "The fourth Brownian kernel is the sum of the three products "
                + "min(s0,s1)min(s2,s3), min(s0,s2)min(s1,s3), and "
                + "min(s0,s3)min(s1,s2).")),
            Describe.Lean(
                DescribeId.Create("brownian-w4-integral"),
                DeclarationHandle.Create(Prefix + "brownianW4_integral"),
                H("Integral of the fourth Brownian kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral of the product of the four profile values times "
                    + "the fourth Brownian kernel over the unit cube equals 3Q(g)^2. "
                    + "The min kernel is bounded by one on the unit square, so each "
                    + "pairing is absolutely integrable. Measure-preserving "
                    + "coordinate permutations reduce all three pairings to two "
                    + "independent copies of the min-kernel integral. Fubini then "
                    + "gives Q(g)^2 for each pairing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-lt-kurtosis-ratio"),
                DeclarationHandle.Create(Prefix + "three_lt_kurtosis_ratio"),
                H("Strict excess kurtosis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every kappa>0, the ratio "
                    + "3*kappa*(2^(2*kappa)-1)*log(2)/(2*(2^kappa-1)^2) "
                    + "is strictly greater than three. Put a=kappa*log(2)>0. "
                    + "Factoring exp(2a)-1 reduces the assertion to "
                    + "2(exp(a)-1)<a(exp(a)+1). The difference on the right "
                    + "minus the left vanishes at zero and has derivative "
                    + "1+(a-1)exp(a)>0; the strict tangent-line inequality "
                    + "1-a<exp(-a) proves this derivative bound."))),
                DescribeRole.Theorem))));
}
