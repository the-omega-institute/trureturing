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
                DescribeId.Create("pair-kernel"),
                DeclarationHandle.Create(Prefix + "pairKernel"),
                H("Profile-weighted Brownian pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real profile g and two coordinates s0,s1, pairKernel "
                    + "is g(s0)g(s1)min(s0,s1), the profile-weighted Brownian "
                    + "covariance kernel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pair-kernel-integrable"),
                DeclarationHandle.Create(Prefix + "pairKernel_integrable"),
                H("Integrability of a profile pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every measurable integrable real profile g on the unit interval, "
                    + "g(s)g(t)min(s,t) is integrable on the unit square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-pair-kernel"),
                DeclarationHandle.Create(Prefix + "integral_pairKernel"),
                H("Integral of a profile pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every measurable integrable real profile g on the unit interval, "
                    + "the integral of g(s)g(t)min(s,t) over the unit square equals Q(g)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pair-product-integrable-and-integral"),
                DeclarationHandle.Create(Prefix + "pair_product_integrable_and_integral"),
                H("Factorization over disjoint coordinate pairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let F and H be integrable real functions on the unit square, "
                    + "and let e be any permutation of the four coordinates. "
                    + "The function F(s(e(0)),s(e(1)))H(s(e(2)),s(e(3))) is integrable "
                    + "on the unit four-cube, and its integral is the product "
                    + "of the integrals of F and H."))),
                DescribeRole.Theorem),
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
                    + "is strictly greater than three. For U with density du/(u*log(2)) "
                    + "on [1,2], strict positive covariance of the positive powers "
                    + "U^kappa and U^kappa gives E[U^(2*kappa)]>E[U^kappa]^2. "
                    + "Evaluating these power moments gives the displayed ratio."))),
                DescribeRole.Theorem))));
}
