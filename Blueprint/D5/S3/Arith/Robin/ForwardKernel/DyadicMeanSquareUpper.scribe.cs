using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class DyadicMeanSquareUpperDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/DyadicMeanSquareUpper.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform short-interval variance bound controls the dyadic mean square of the complete forward response.",
        H("Dyadic mean-square upper bound"),
        Blocks(
            Paragraph(Text(
                "Write E(x)=psi(x)-x, H(x)=x^(4/5), and "
                + "D(x,theta)=E((1+theta)*x)-E(x), with the complete Chebyshev psi. "
                + "Assume constants A>0 and Y>=2 such that, for every X>=Y and "
                + "0<theta<=1, the integral of D(x,theta)^2 over [X,2X] is at most "
                + "A*theta*X^2*log(2/theta)^2. This is the explicit "
                + "ShortIntervalMeanSquareBound hypothesis; no separate Riemann "
                + "hypothesis is used.")),
            Describe.Lean(
                DescribeId.Create("forward-kernel-dyadic-mean-square-upper"),
                DeclarationHandle.Create(Prefix + "forward_kernel_dyadic_mean_square_upper"),
                H("The dyadic upper estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exist C>0 and X0>=3 such that, for every X>=X0, "
                        + "the integral of forwardResponse(x)^2/x over [X,2X] "
                        + "is at most C*X^(1/5)*log(X)^2.")),
                    Paragraph(Text(
                        "The substitution u=theta*x expresses the response as "
                        + "sqrt(x)*x/H(x)^2 times the integral of D(x,theta) "
                        + "multiplied by w((1+theta)*x)/w(x), for "
                        + "0<=theta<=H(x)/x. Positivity and monotonicity of w "
                        + "bound this ratio between zero and one. Cauchy–Schwarz "
                        + "therefore bounds the squared response divided by x "
                        + "by x/H(x)^3 times the integral of D(x,theta)^2. "
                        + "For x in [X,2X], enlarge the theta interval to "
                        + "[0,a], where a=X^(-1/5), and bound x/H(x)^3 "
                        + "by X^(-7/5). Bounded measurable increments justify "
                        + "Fubini on this rectangle. For X>=16^5, the function "
                        + "theta*log(2/theta)^2 is increasing up to a<=1/16. "
                        + "The assumed variance estimate then bounds the double "
                        + "integral by A*X^2*a^2*log(2/a)^2. Finally "
                        + "log(2/a)<=2*log(X), giving C=4*A and "
                        + "X0=max(Y,16^5)."))),
                DescribeRole.Theorem))));
}
