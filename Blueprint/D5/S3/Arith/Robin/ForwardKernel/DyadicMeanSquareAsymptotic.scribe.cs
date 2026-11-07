using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class DyadicMeanSquareAsymptoticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareAsymptotic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The moving-length mean-square limit transfers to the original forward response and yields a point in every sufficiently large dyadic interval.",
        H("Dyadic mean-square asymptotic and point extraction"),
        Blocks(
            Paragraph(Text(
                "Write E(x)=psi(x)-x, H(x)=x^(4/5), and P(h,x)=h^(-2) "
                + "times the integral of E(x+u)-E(x) for 0<=u<=h. "
                + "The scale is S(X)=X^(1/5)*log(X). The assumptions are the von Koch bound, the uniform short-interval "
                + "mean-square bound, and the uniform cumulative variance band asymptotic.")),
            Describe.Lean(
                DescribeId.Create("dyadic-point-weight-integral-tendsto"),
                DeclarationHandle.Create(Prefix + "dyadic_point_weight_integral_tendsto"),
                H("The point-extraction weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral of x^(1/5)*log(x)/x over [X,2X], divided "
                    + "by S(X), tends to 5*(2^(1/5)-1). Substitution x=X*v "
                    + "makes the quotient the integral of v^(-4/5) over "
                    + "[1,2], plus the fixed integral of v^(-4/5)*log(v) "
                    + "divided by log(X)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-kernel-dyadic-mean-square-asymptotic"),
                DeclarationHandle.Create(Prefix + "forward_kernel_dyadic_mean_square_asymptotic"),
                H("Transfer to the original forward response"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume the von Koch error bound, the uniform short-interval "
                    + "mean-square bound, and the uniform cumulative variance band asymptotic. "
                    + "The moving-length theorem gives the limit (2^(1/5)-1)/3 "
                    + "for the normalized square integral of P(H(x),x). The integral of "
                    + "forwardResponse(x)^2/x has the same normalized limit. "
                    + "The unweighted response is sqrt(x)*P(H(x),x). "
                    + "After division by sqrt(x), the difference from the "
                    + "original response has normalized squared integral "
                    + "tending to zero. The L2 reverse triangle inequality "
                    + "therefore preserves the mean-square limit. "
                    + "The three hypotheses are assumptions; the von Koch bound and the short-interval estimate follow from the Riemann hypothesis, and the cumulative variance asymptotic follows from the Riemann hypothesis together with the strong pair-correlation conjecture, so the theorem is conditional."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-kernel-dyadic-point"),
                DeclarationHandle.Create(Prefix + "forward_kernel_dyadic_point"),
                H("A point in each sufficiently large dyadic interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the von Koch bound and the two uniform variance hypotheses, "
                    + "the normalized integral of forwardResponse(x)^2/x tends to "
                    + "(2^(1/5)-1)/3. For every 0<c<1/sqrt(15), every "
                    + "sufficiently large interval [X,2X] contains a point "
                    + "x with absolute response at least "
                    + "c*x^(1/10)*sqrt(log(x)). Otherwise squaring and "
                    + "integrating the pointwise strict bound would bound "
                    + "the mean square by c^2 times the point-extraction "
                    + "weight, contradicting their limiting ratio 1/15. "
                    + "The three hypotheses are assumptions; the von Koch bound and the short-interval estimate follow from the Riemann hypothesis, and the cumulative variance asymptotic follows from the Riemann hypothesis together with the strong pair-correlation conjecture, so the theorem is conditional."))),
                DescribeRole.Theorem))));
}
