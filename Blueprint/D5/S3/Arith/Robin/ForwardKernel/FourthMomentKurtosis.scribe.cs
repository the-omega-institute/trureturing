using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FourthMomentKurtosisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthMomentKurtosis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth Brownian interface determines two dyadic moment limits and positive excess kurtosis.",
        H("Fixed dyadic positive excess kurtosis"),
        Blocks(
            Paragraph(Text(
                "Let E be a real locally bounded Borel measurable function, "
                + "let 0<alpha<theta<beta<1, and let g be a real measurable "
                + "integrable profile on the unit interval. Assume the cumulative "
                + "variance asymptotic and fourth-moment bound throughout the "
                + "exponent band. Write kappa=1-theta, "
                + "Q(g)=integral g(s)g(t)min(s,t) ds dt, and "
                + "Z_X(x)=profileResponse(E,theta,g,x)/sqrt(X^kappa log(X)). "
                + "Expectations use dx/(x log(2)) on [X,2X].")),
            Describe.Lean(
                DescribeId.Create("fixed-dyadic-positive-excess-kurtosis"),
                DeclarationHandle.Create(Prefix + "fixed_dyadic_positive_excess_kurtosis"),
                H("Second and fourth moments with strict excess kurtosis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume for every four unit-interval parameters that the "
                        + "mixed normalized increment moment with position factor "
                        + "(x/X)^(2*kappa) tends to c4*kappa^2 times the sum of "
                        + "the three Brownian covariance pairings, where "
                        + "c4=(2^(2*kappa)-1)/(2*kappa*log(2)). Then "
                        + "E[Z_X^2] tends to L2=(2^kappa-1)*Q(g)/log(2), "
                        + "and E[Z_X^4] tends to "
                        + "L4=3*kappa*(2^(2*kappa)-1)*Q(g)^2/(2*log(2)). "
                        + "If g is not almost everywhere zero, 3*L2^2<L4.")),
                    Paragraph(Text(
                        "The second limit follows from the profile-kernel "
                        + "dyadic mean-square asymptotic and the logarithmic "
                        + "probability-measure conversion. The fourth-moment "
                        + "band bound supplies the uniform absolute-moment "
                        + "part of the fourth moment interface; the Brownian "
                        + "pairing function is measurable and the assumed "
                        + "mixed-moment limits supply its remaining part. "
                        + "Applying the general moment-transfer theorem with "
                        + "k=4 and the Brownian pairing integral gives L4. "
                        + "Positivity of Q(g) and the strict dyadic kurtosis "
                        + "ratio inequality give 3*L2^2<L4.")),
                    Paragraph(Text(
                        "This conclusion is conditional on the fourth-order "
                        + "Brownian interface. It does not establish that "
                        + "interface for the Chebyshev error or assert "
                        + "convergence in distribution."))),
                DescribeRole.Theorem))));
}
