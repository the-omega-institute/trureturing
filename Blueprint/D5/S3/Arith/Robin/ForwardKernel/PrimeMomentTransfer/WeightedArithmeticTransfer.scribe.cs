using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class WeightedArithmeticTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedArithmeticTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "BV weighted arithmetic moments agree with their quadratic formal integrals up to a uniform square-root error.",
        H("BV weighted arithmetic transfer"),
        Blocks(
            Paragraph(Text(
                "MeanSquareHL(q,SS,beta) is the uniform mean-square correlation hypothesis on real cutoffs "
                + "N<=y<=2N and injective positive shift tuples in [1,K], with 1<=K<=M N^beta. "
                + "Chan, A note on primes in short intervals, International Journal of Number Theory 2 "
                + "(2006), 105–110, is the single-interval mean-square precedent. The overlapping "
                + "mixed-moment transfer with supported BV weights here is repo-derived. The arbitrary-order statement extends the arithmetic mechanism of Lemma 498.4 and Corollary 498.6 in Fibonacci Analytic Frontier Interfaces II.")),
            Describe.Lean(
                DescribeId.Create("polynomial-weight-integrable"),
                DeclarationHandle.Create(Prefix + "polynomial_weight_integrable"),
                H("Integrability of polynomial logarithmic weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For N at least two, a supported bounded variation weight w and any real polynomial p, the function w(x/N) p(log x) is interval integrable over [N,2N]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("formal-weight-integrable"),
                DeclarationHandle.Create(Prefix + "formal_weight_integrable"),
                H("Integrability of weighted formal moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every singular-series function, length, tuple of endpoints and supported bounded variation weight, the weighted formal moment w(x/N) Phi(log x) is interval integrable over [N,2N] when N is at least two. Each tuple contributes a finite sum of polynomial logarithmic weights."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arithmetic-transfer"),
                DeclarationHandle.Create(Prefix + "arithmetic_transfer"),
                H("Weighted arithmetic moments of arbitrary fixed order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume zero less than alpha less than beta less than one, the uniform "
                        + "mean-square hypothesis through the natural order q, and singular-series values one "
                        + "on the empty set and on singletons. Fix M at least one and positive "
                        + "epsilon. There is a nonnegative C such that, for every sufficiently "
                        + "large real N, every integer H between N to alpha and N to beta, "
                        + "every supported BV weight w with supremum bound plus variation at most B, "
                        + "and every k intervals with 1<=k<=q in [0,M], the discrete weighted product "
                        + "of centred von Mangoldt interval sums differs from the integral of "
                        + "w(x/N) times Phi(log x) by at most C B N to the power one half plus "
                        + "epsilon times H to the number of intervals. C and the threshold for N "
                        + "precede all choices of H, weight, number of intervals, and endpoints.")),
                    Paragraph(Text(
                        "The quadratic reduction expresses every repeated-index tuple using "
                        + "centred distinct products with polynomial logarithmic coefficients. "
                        + "Only a fixed finite family of coefficient polynomials occurs for tuples "
                        + "of length at most q, using the reduction polynomials for multiplicities from zero to q and products of at most q factors. Group all tuple-subset contributions by their "
                        + "coefficient polynomial and apply the aggregate centred BV correlation "
                        + "estimate to each group, using K=floor(M H). Its K^k bound is at most "
                        + "M^q H^k for k<=q. Summing over the fixed coefficient family and using "
                        + "a smaller positive mean-square error exponent absorbs the logarithms. The repeated-shift "
                        + "collision estimate accounts for proper prime powers and for replacing "
                        + "log(n+d) by log n. This transfer uses no singular-series interval "
                        + "asymptotic hypothesis."))),
                DescribeRole.Theorem))));
}
