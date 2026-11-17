using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class ZeroAbscissaMertensLowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unconditional lower power envelope of the actual arithmetic B",
        H("Transport from the actual zero abscissa to the Mertens error"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-b-zero-abscissa-lower-power"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ZeroAbscissaMertensLowerBound.actual_B_zero_abscissa_lower_power"),
                H("Every positive exponent margin on all sufficiently large real endpoints"),
                StatementSource.FromAuthor(LowerPowerClaim()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write Theta=KappaGap.zeroAbscissa, the supremum of the real parts of the actual "
                        + "nontrivial zeta zeros, and B=RHSharpArithmeticEnvelope.B. Thus "
                        + "B(x)=Mertens.E₃(x)+log(log(Chebyshev.theta(x)))-log(log(x)). "
                        + "For every real epsilon>0 there are real constants C>=0 and T>=2 such that "
                        + "-C*x^(Theta-1+epsilon)<=B(x) for every real x>=T. The constants may depend "
                        + "on epsilon. There is no Riemann Hypothesis assumption, and the supremum "
                        + "need not be attained.")),
                    Paragraph(Text(
                        "The prime number theorem gives theta(x)/x->1, hence eventually "
                        + "x/2<=theta(x)<=3*x/2. The identity "
                        + "log(log(theta(x)))-log(log(x))=log(1+log(theta(x)/x)/log(x)) "
                        + "then proves that this difference tends to zero. Mertens.E₃.bound' "
                        + "also gives E₃(x)->0, so B(x)->0. If Theta-1+epsilon>=0, the eventual "
                        + "bound B(x)>=-1 and x^(Theta-1+epsilon)>=1 prove the conclusion with C=1.")),
                    Paragraph(Text(
                        "Otherwise set beta=Theta+epsilon/2. The RH/right-strip dichotomy and the "
                        + "existence of a nontrivial zero give Theta>=1/2, so 1/2<beta<1. "
                        + "ZeroAbscissaPower.actual_zero_abscissa_power_bound supplies the unconditional "
                        + "actual psi estimate at exponent beta. ZeroFreeStripMertensEnvelope.theta_power_bound "
                        + "uses the public Chebyshev bound "
                        + "psi(x)-theta(x)<=H*sqrt(x) to transfer it to abs(theta(x)-x)<=K*x^beta "
                        + "on a sufficiently large real tail, with K>=0.")),
                    Paragraph(Text(
                        "Put w(t)=(log(t)+1)/(t^2*log(t)^2), Jtheta(x)=integral_(t>x)(theta(t)-t)*w(t), "
                        + "and N(x)=log(log(theta(x)))-log(log(x))-(theta(x)-x)/(x*log(x)). "
                        + "ThetaTailRobinWitness.theta_tail_mertens_robin gives integrability and the "
                        + "exact decomposition B=Jtheta+(E₃+E₂p)+N for every x>=2. For t>=exp(1), "
                        + "0<=w(t)<=2/t^2. Integration of the power majorant gives "
                        + "abs(Jtheta(x))<=(2*K/(1-beta))*x^(beta-1). This uses the actual infinite "
                        + "Lebesgue tail, without differentiating theta or assuming cancellation of zero phases.")),
                    Paragraph(Text(
                        "Strict log-log tangency in both directions, with y>=x/2 and x>=4, yields "
                        + "abs(log(log(y))-log(log(x)))<=4*abs(y-x)/(x*log(x)). "
                        + "Consequently N(x)>=-5*K*x^(beta-1) on the same eventual domain. "
                        + "RHSharpArithmeticEnvelope.finite_cancellation supplies abs(E₃(x)+E₂p(x))<=4/x. "
                        + "Since beta>1/2 and x>=1, 1/x<=x^(beta-1). Adding these bounds gives "
                        + "B(x)>=-(2*K/(1-beta)+5*K+4)*x^(beta-1). Finally beta-1<=Theta-1+epsilon "
                        + "and the coefficient is nonnegative, so increasing the exponent preserves "
                        + "the asserted lower bound.")),
                    Paragraph(Text(
                        "The result controls B at the actual zero abscissa. It neither identifies "
                        + "that abscissa with one half nor proves RH or Robin's inequality."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesClaim(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula LowerPowerClaim()
    {
        var epsilon = F.Id("epsilon");
        var c = F.Id("C");
        var t = F.Id("T");
        var x = F.Id("x");
        var exponent = Add(Subtract(F.Id("Theta"), D(1)), epsilon);
        var bound = AtMost(Multiply(new Formula.Negate(c), new Formula.Power(x, exponent)),
            new Formula.FunctionCall(FormulaIdentifier.Create("B"), [x]));
        return Disp(All("epsilon", Real, ImpliesClaim(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, epsilon),
            ExistsOne("C", Real, ExistsOne("T", Real,
                And(AtMost(D(0), c), And(AtMost(D(2), t),
                    All("x", Real, ImpliesClaim(AtMost(t, x), bound)))))))));
    }
}
