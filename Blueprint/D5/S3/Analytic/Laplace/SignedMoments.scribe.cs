using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class SignedMomentsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Laplace/SignedMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derivatives and positive-part bounds for signed Laplace moments",
        H("Signed Laplace moments"),
        Blocks(
            Paragraph(Text("The positive-part moment inequality has no integrability or "
                + "measurability premise. If the signed real moment is not integrable, "
                + "multiplying the complex integrand by a continuous unit-modulus phase "
                + "shows that it too is not integrable. Both signed Bochner integrals "
                + "then have the total value zero. The Laplace derivative and window "
                + "applications establish genuine absolute integrability separately.")),
            Paragraph(Text("Let h be a measurable real function. Suppose its exponentially "
                + "weighted integral on the nonnegative axis is absolutely convergent at every "
                + "real parameter greater than a. The complex transform uses exp(-zu). The "
                + "moment of order k inserts the factor u to the power k into this integral.")),
            Describe.Lean(DescribeId.Create("absolute-polynomial-moments"),
                DeclarationHandle.Create(Module + "absolute_moment_integrable"),
                H("Polynomial weights preserve interior exponential convergence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each natural k and real sigma greater than a, "
                    + "the function u to the power k times the absolute value of h(u), damped "
                    + "by exp(-sigma u), is integrable. The measure with density the absolute "
                    + "value of h converts this statement into the polynomial moment theorem "
                    + "for a moment-generating function."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-polynomial-moments"),
                DeclarationHandle.Create(Module + "moment_integrable"),
                H("Absolute convergence of the complex moments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every complex z with real part greater than a, "
                    + "each complex moment is absolutely integrable. Its integrand norm is "
                    + "the corresponding absolute real moment at the real part of z."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-moment-derivative"),
                DeclarationHandle.Create(Module + "moment_hasDerivAt"),
                H("Differentiating a signed moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivative of the moment of order k is minus the "
                    + "moment of order k+1. Choose a real damping parameter strictly between "
                    + "a and the real part of z. On the resulting complex neighborhood, the "
                    + "absolute moment at that parameter dominates the differentiated kernel. "
                    + "Dominated differentiation therefore applies without a sign restriction "
                    + "on h."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-laplace-higher-derivatives"),
                DeclarationHandle.Create(Module + "iteratedDeriv_laplace"),
                H("All derivatives are actual signed moments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural k and every z with real part greater "
                    + "than a, the derivative of order k of the signed Laplace transform is "
                    + "(-1) to the power k times the moment of order k. The equality concerns "
                    + "the actual integral, and follows by induction using equality of germs "
                    + "throughout the open half-plane."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-center-signed-moment"),
                DeclarationHandle.Create(Module + "alternating_derivative_real"),
                H("The real center gives the signed real moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a real center sigma greater than a, multiply the "
                    + "derivative of order k by (-1) to the power k and divide by k factorial. "
                    + "The real part is exactly the real signed moment of order k divided "
                    + "by k factorial. The two alternating signs cancel, and integration "
                    + "commutes with the real embedding."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-part-moment-bound"),
                DeclarationHandle.Create(Module + "moment_norm_add_real_le"),
                H("The one-sided bound for signed moments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix a natural k and a complex z, "
                    + "with arbitrary real density h. "
                    + "The inequality uses total Bochner integrals and needs no premises. "
                    + "The norm of the complex moment, plus that real signed moment, is at "
                    + "most twice the moment with h replaced by max(h,0). The triangle "
                    + "inequality and the identity absolute(h)+h=2 max(h,0) give this estimate. "
                    + "No eventual sign or positivity assumption is imposed on h."))),
                DescribeRole.Theorem))));
}
