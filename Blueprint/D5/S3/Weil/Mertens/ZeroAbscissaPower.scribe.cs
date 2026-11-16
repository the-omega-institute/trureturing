using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class ZeroAbscissaPowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/ZeroAbscissaPower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted differences of the complete integrated zero formula give the unconditional Chebyshev power bound at the zero abscissa.",
        H("The actual zero abscissa and the Chebyshev error"),
        Blocks(
            Paragraph(Text(
                "Write rho(k)=actualZero(k), retaining every analytic zero occurrence with its exact "
                + "multiplicity and both imaginary signs. The coefficient is 1/(rho(k)*(1-rho(k))). "
                + "The complete absolutely convergent series actualH(y) is the sum of this coefficient "
                + "times exp(y*rho(k)). The unconditional integrated formula is "
                + "actualH(y)=U(exp(y))-log(2*pi)+trivialT(y) for y>0. Therefore V(x)=U(x)/x "
                + "is actualH(log(x))/x plus (log(2*pi)-trivialT(log(x)))/x. The coefficient has "
                + "positive sign. The complete arithmetic tail identity gives V=-Q and hence "
                + "V(b)-V(a)=integral((psi(t)-t)/t^2,a..b) whenever a,b>=2.")),
            Describe.Lean(
                DescribeId.Create("actual-primitive-low-high"),
                DeclarationHandle.Create(Prefix + "actual_primitive_low_high"),
                H("A finite head and an infinite tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is C>0 such that, for all real beta,x,a,b,T with 0<=beta<=1, "
                        + "Re(rho(k))<=beta for every k, x>=4, a>=x/2, b>=x/2 and T>=2, "
                        + "the norm of actualH(log(b))/b-actualH(log(a))/a is at most "
                        + "C*abs(b-a)*x^(beta-2)*(1+log(T))^2+C*x^(beta-1)*(1+log(T))/T. "
                        + "The constant is independent of beta and all four real scale parameters.")),
                    Paragraph(Text(
                        "For one occurrence put f(s)=s^(rho-1)/(rho*(1-rho)). Its derivative "
                        + "is -s^(rho-2)/rho. The unconditional unit-window zero count gives "
                        + "N(T)<=A*T*(1+log(T)). The existing multiplicity-weighted Stieltjes "
                        + "identities then bound the finite low-height reciprocal norm sum by "
                        + "B*(1+log(T))^2 and every finite quadratic tail band by "
                        + "B*(1+log(T))/T, uniformly in its upper endpoint. Finite analytic-order "
                        + "fibers transport these sums exactly to the natural occurrence indices. "
                        + "Bounding every finite partial sum proves the same bound for the true "
                        + "infinite high-height tail. The unconditional height-ten theorem makes "
                        + "the height-two head empty.")),
                    Paragraph(Text(
                        "The derivative estimate is used only for the low-height terms. The "
                        + "high-height terms are bounded at their two endpoints using absolute "
                        + "summability. In particular no derivative of the complete infinite "
                        + "zero series, phase cancellation, zero simplicity or contour-height "
                        + "selection is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-psi-low-high"),
                DeclarationHandle.Create(Prefix + "actual_psi_low_high"),
                H("The full weighted finite-difference estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is C>0 such that for every 0<=beta<=1 bounding all actual "
                        + "zero real parts, every x>=4, 1<=h<=x/2 and T>=2, the actual "
                        + "Chebyshev error satisfies abs(psi(x)-x)<=h+C*x^beta*(1+log(T))^2"
                        + "+C*x^(beta+1)*(1+log(T))/(h*T). All quantifiers are over real "
                        + "parameters except the natural occurrence index, and C is uniform in them.")),
                    Paragraph(Text(
                        "Monotonicity of psi gives (psi(x)-x-h)*Iplus<=V(x+h)-V(x) "
                        + "and V(x)-V(x-h)<=(psi(x)-x+h)*Iminus, where "
                        + "Iplus=h/(x*(x+h)) and Iminus=h/(x*(x-h)). Both weights are "
                        + "positive and their inverses are at most 2*x^2/h. The elementary "
                        + "correction G has derivative "
                        + "G'(s)=(-log(1-exp(-2*log(s)))/2-log(2*pi))/s^2, bounded "
                        + "by a fixed constant times s^(-2) "
                        + "for s>=2; its divided difference therefore contributes only a fixed "
                        + "constant, absorbed by x^beta*(1+log(T))^2. The interval x-h>=2 "
                        + "includes its boundary. Monotonicity handles both signs of the error "
                        + "and every prime-power jump without a continuity assumption on psi."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-zero-abscissa-power-bound"),
                DeclarationHandle.Create(Prefix + "actual_zero_abscissa_power_bound"),
                H("Every positive exponent margin, at every real x>=2"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Theta=KappaGap.zeroAbscissa, the supremum of the real parts "
                        + "of the actual nontrivial zeros. For every real epsilon>0 there "
                        + "exists a real C such that abs(psi(x)-x)<=C*x^(Theta+epsilon) "
                        + "for every real x>=2. The supremum need not be attained.")),
                    Paragraph(Text(
                        "If Theta<1, take h=x^Theta and T=x for sufficiently large x. "
                        + "Then 1<=h<=x/2, and the high-height term is C*(1+log(x)). "
                        + "Together with the head estimate this gives a constant times "
                        + "x^Theta*(1+log(x))^2. The logarithm is smaller than any positive "
                        + "power eventually. Chebyshev's linear bound controls the remaining "
                        + "initial interval. If Theta=1, the same linear bound proves the "
                        + "claimed power estimate directly. These arguments also retain "
                        + "the endpoint Theta=0 in the first case.")),
                    Paragraph(Text(
                        "The result supplies the hTheta premise of the existing KappaGap "
                        + "forward-response theorems by direct application. It estimates "
                        + "the error at the actual zero abscissa; it does not assert that "
                        + "the abscissa equals one half or that every n>5040 satisfies "
                        + "Robin's inequality."))),
                DescribeRole.Theorem))));
}
