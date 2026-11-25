using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class MovingFejerGaussianPrincipalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/MovingFejerGaussianPrincipal";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A growing fourth-moment window captures the Gaussian principal contribution of the Fejer integral.",
        H("Gaussian principal coefficient of the moving Fejer integral"),
        Blocks(
            Paragraph(Text("For finite families of real frequencies g_n and real weights w_n, let S_n(t) be their complex Fourier score, W_n their total weight, and M_n(k) the sum over ordered pairs of w_n(i)w_n(j)(g_n(i)-g_n(j))^k. Set s_n=sqrt(n M_n(2)/2), R_n=M_n(4)/(n M_n(2)^2), and P_n(u)=|S_n(u/s_n)|^(2n). For real sequences rho and A, write I(n) for 1/(2 pi) times the oriented integral of sinc(rho(n)u/2)^2 P_n(u) from -A(n) to A(n).")),
            Describe.Lean(DescribeId.Create("central-fejer"), DeclarationHandle.Create(Owner + ".central_fejer_gaussian_limit"),
                H("Central Gaussian integral limit"), StatementSource.FromAuthor(Principal()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume eventually all pair products are nonnegative, W_n=1, M_n(2)>0, and A(n)^2 M_n(4)<=6 n M_n(2)^2. Assume also rho tends to zero and A tends to positive infinity. The window condition implies 0<=R_n<=6/A(n)^2 eventually, so R_n tends to zero. The central power limit gives pointwise convergence of P_n to exp(-u^2), and the sinc factor tends to one at every fixed u. On the inner half-window the global fourth-moment estimate provides an integrable Gaussian envelope. Extend by zero outside this half-window and apply dominated convergence. On either outer half-window the score power is bounded by exp(-u^2(1-u^2/A(n)^2)), which is at most exp(-(A(n)/4)(A(n)-|u|)). The sinc factor has square at most one. Integrating the two outer halves gives a total bound of 8/A(n), tending to zero. The integral of exp(-u^2) is sqrt(pi), yielding the coefficient 1/(2 sqrt(pi)). For any eventually nonnegative R tending to zero, the choice A(n)=1/sqrt(R(n)+1/(n+1)) tends to positive infinity and eventually A(n)^2 R(n)<1, furnishing an admissible window.")),
                    Paragraph(Text("With physical resolution eta_n>0 and scale s_n>0, the angular Fejer kernel is K_eta(t)=eta/(2 pi) sinc(eta t/2)^2. Substituting u=s_n t and rho_n=eta_n/s_n identifies I(n) with s_n/eta_n times the kernel-weighted score-power integral on [-A(n)/s_n,A(n)/s_n]. Contributions outside this interval require independent control."))), DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula Limit(Formula body) =>
        F.Seq(F.Lim, F.Underscore, F.Grp(I("n"), F.Sp, F.To, F.Sp, F.Infty), F.Sp, body);
    private static Formula Div(Formula a, Formula b) => F.Seq(F.Frac, F.Grp(a), F.Grp(b));
    private static Formula Pow(Formula a, byte n) => F.Seq(a, F.Caret, F.Grp(F.D(n)));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Eventually(Formula a) => Call("Eventually", a);
    private static Formula M(byte k) => Call("M", F.D(k));
    private static Formula Principal()
    {
        Formula n = I("n"), a = Call("A", n);
        Formula hwin = Eventually(Le(Multiply(Pow(a, 2), M(4)), Multiply(Multiply(F.D(6), n), Pow(M(2), 2))));
        Formula momentConditions = And(Eventually(Call("PairNonnegative", I("w"))),
            And(Eventually(Equal(I("W"), F.D(1))), Eventually(Lt(F.D(0), M(2)))));
        Formula limitConditions = And(Equal(Limit(Call("rho", n)), F.D(0)), Equal(Limit(a), F.Infty));
        Formula assumption = And(momentConditions, And(limitConditions, hwin));
        return F.Disp(Imp(assumption, Equal(Limit(Call("I", n)), Div(F.D(1), Multiply(F.D(2), F.Seq(F.Sqrt, F.Grp(F.Pi)))))));
    }
}
