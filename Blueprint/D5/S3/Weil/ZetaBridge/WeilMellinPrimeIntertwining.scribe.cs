using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilMellinPrimeIntertwiningDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining.";
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), M = F.Id("M"), h = F.Id("h"), x = F.Id("x");
        Formula d = F.Id("d"), A = F.Id("A"), t = F.Id("t"), n = F.Id("n");
        Formula p = Call("windowMellinSum", a, M, h);
        Formula q = Call("windowMellinSum", a, M, Call("LogTimesSeed", h));
        Formula r = Call("OddPart", p);
        Formula hypotheses = Call("And",
            Call("LessEqual", Call("exp", Call("mul", D(2), a)), M),
            Call("UpperSupport", h, Call("exp", a)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The actual weighted prime translations on an arithmetic Mellin model "
                + "collapse to the logarithmic seed, with its full window and parity correction retained.",
            H("Mellin Prime Intertwining"),
            Blocks(
                Paragraph(Text(
                    "Write E(h)=windowMellinSum(a,M,h), Xf(x)=x*f(x), and Rf(x)=f(-x). "
                    + "The same half-density and factor four are used by the existing "
                    + "WeilPolynomialMellinWindow. The arithmetic input is Mathlib's "
                    + "vonMangoldt_sum. There is no alternative zeta, Gamma or Weil form.")),
                Describe.Lean(DescribeId.Create("window-mellin-sum"),
                    DeclarationHandle.Create(Owner + "windowMellinSum"), H("Supported arithmetic synthesis"),
                    StatementSource.FromAuthor(Disp(Seq(Call("apply", p, x), Eq,
                        Call("IndicatorIcc", Seq(Minus, a), a,
                            Call("mul", D(4), Call("exp", Call("div", x, D(2))),
                                Call("SumIcc", D(1), M, Call("apply", h,
                                    Call("mul", n, Call("exp", x))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "a is real, M natural and h complex-valued on the reals. "
                        + "Closed endpoints make reflection exact. The difference from the "
                        + "earlier Ioc convention is isolated in the agreement theorem."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("prime-forward"),
                    DeclarationHandle.Create(Owner + "primeForward"), H("Actual one-sided prime block"),
                    StatementSource.FromAuthor(Disp(Seq(Call("primeForward", a, M, F.Id("f"), x), Eq,
                        Call("IndicatorIcc", Seq(Minus, a), a,
                            Call("SumIcc", D(1), M, Call("mul",
                                Call("div", Call("vonMangoldt", n), Call("sqrt", n)),
                                Call("apply", F.Id("f"), Seq(x, Plus, Call("log", n))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The original Lambda(n)/sqrt(n) coefficients and translated function "
                        + "values are specified independently. All prime powers are included. "
                        + "The n=1 term vanishes; terms beyond exp(2a) vanish on the window, "
                        + "and a term exactly at that threshold affects only an endpoint."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("prime-symmetric"),
                    DeclarationHandle.Create(Owner + "primeSymmetric"), H("Both prime translation directions"),
                    StatementSource.FromAuthor(Disp(Seq(Call("primeSymmetric", a, M, F.Id("f"), x), Eq,
                        Call("IndicatorIcc", Seq(Minus, a), a,
                            Call("SumIcc", D(1), M, Call("mul",
                                Call("div", Call("vonMangoldt", n), Call("sqrt", n)),
                                Call("add", Call("apply", F.Id("f"), Seq(x, Plus, Call("log", n))),
                                    Call("apply", F.Id("f"), Seq(x, Minus, Call("log", n)))))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is the unsigned symmetric translation block. Its negative gives "
                        + "the prime contribution to the canonical Weil operator. Reflection "
                        + "relates its two directions, but they are not identified before proof."))),
                    DescribeRole.Definition),
                Paragraph(Text(
                    "The same primeSymmetric action has a concrete Hilbert-space application. "
                    + "For real a, use H=L2(R,C;dx), P_a u=1_{[-a,a]}u, "
                    + "U_s u(x)=u(x-s), and T_{a,s}=P_a U_s P_a. The measure is Lebesgue "
                    + "measure and the Lp exponent is exactly 2. Mathlib's "
                    + "Lp.compMeasurePreserving linear isometry supplies U_s. The actual "
                    + "supported carrier is ker(P_a-id), equivalently the classes zero "
                    + "almost everywhere outside [-a,a]. On this carrier, "
                    + "T_{a,s}u=1_{[-a,a]}(x)u(x-s) almost everywhere. Indicator "
                    + "multiplication is an orthogonal projection, so norm(T_{a,s})<=1, "
                    + "adjoint(T_{a,s})=T_{a,-s}, and reflection R u(x)=u(-x) obeys "
                    + "R T_{a,s}=T_{a,-s} R. These are actual L2 operators, with no "
                    + "pointwise endpoint normalization of their representatives.")),
                Paragraph(Text(
                    "If 2*a<=abs(s), then T_{a,s}=0. For x strictly between -a and a, "
                    + "membership of x-s in [-a,a] would imply abs(s)<2*a. The two "
                    + "possible outer endpoints are Lebesgue-null, which proves the "
                    + "operator equality also when abs(s)=2*a. For a<=0 the supported "
                    + "L2 carrier is zero. Thus the active operator channels have the "
                    + "strict cutoff log(n)<2*a; equality is removed by almost-everywhere "
                    + "equality of operators, rather than by a convention for f(a) or f(-a).")),
                Paragraph(Text(
                    "Use exactly PrimeJumpDecomposition.primeWeight(n)=Lambda(n)/sqrt(n), "
                    + "N_a=floor(exp(2*a)), and its existing "
                    + "S_a=activePrimePowers(a)={1<=n<=N_a : Lambda(n)!=0}. "
                    + "The unsigned compressed block is "
                    + "B_a=sum_{n in S_a} primeWeight(n)*(T_{a,log(n)}+T_{a,-log(n)}). "
                    + "All prime powers n=p^k with k>=1 are retained, with coefficient "
                    + "log(p)/sqrt(p^k). Real nonnegative coefficients, the two contraction "
                    + "bounds and the finite-sum triangle inequality give "
                    + "norm(B_a)<=2*sum_{n in S_a} primeWeight(n)="
                    + "2*totalPrimeWeight(a). The bound uses the original nonnegative "
                    + "weights. Each paired shift is selfadjoint and commutes with R, "
                    + "so B_a has both properties.")),
                Paragraph(Text(
                    "Filtering by Lambda(n)!=0 discards zero summands only. Consequently "
                    + "the same B_a is the full sum over 1<=n<=N_a and, independently, "
                    + "its sum can be filtered by the strict inequality log(n)<2*a. "
                    + "The original totalPrimeWeight(a) still uses S_a, which can include "
                    + "a positive-weight equality channel even though that compressed "
                    + "operator is zero. For every u in ker(P_a-id), the actual representative "
                    + "of B_a u is almost everywhere "
                    + "1_{[-a,a]}(x)*sum_{1<=n<=N_a}(Lambda(n)/sqrt(n))*"
                    + "(u(x+log(n))+u(x-log(n))). This is precisely the existing "
                    + "primeSymmetric(a,N_a,u), including both signs and the n=1 zero term. "
                    + "Since U_s uses x-s, primeForward uses the T_{a,-log(n)} direction. "
                    + "The prime contribution to the canonical Weil operator retains "
                    + "the existing minus sign, -B_a.")),
                Paragraph(Text(
                    "For every natural cutoff M with exp(2*a)<=M, the same B_a also "
                    + "agrees almost everywhere with primeSymmetric(a,M,u) on the supported "
                    + "carrier. Indeed floor(exp(2*a))<=M, and both finite index sets have "
                    + "the same filter log(n)<2*a: an active n is positive, so "
                    + "log(n)<2*a implies n<exp(2*a) and n<=floor(exp(2*a)). "
                    + "Discarded paired shifts vanish, including the equality channel. "
                    + "This supplies the exact natural-cutoff transfer used by the "
                    + "pointwise Mellin identity below.")),
                Paragraph(Text(
                    "Keep the original upper-support premise h(t)=0 for t>exp(a), "
                    + "the same M, and p=windowMellinSum(a,M,h). If p is in "
                    + "MemLp(p,2,volume), reflection and linearity put its even part "
                    + "p_e(x)=(p(x)+p(-x))/2 in the supported L2 carrier. The existing "
                    + "prime_even_mellin_identity then identifies B_a p_e almost "
                    + "everywhere with q(x)+q(-x)-2*x*r(x)-primeForward(a,M,r,x)"
                    + "-primeForward(a,M,r,-x), where q=windowMellinSum(a,M,log(t)*h) "
                    + "and r=(p-p composed with negation)/2. The whole odd correction "
                    + "is retained. This application requires only the separate MemLp "
                    + "premise on p; it asserts no MemLp of the seed h or of q "
                    + "individually. Upper support alone does not imply square "
                    + "integrability. The Gamma action and its closed form domain "
                    + "require their own common-window identification.")),
                Describe.Lean(DescribeId.Create("cut-polynomial-seed"),
                    DeclarationHandle.Create(Owner + "cutPolynomialSeed"), H("The existing polynomial seed with upper cutoff"),
                    StatementSource.FromAuthor(Disp(Seq(Call("cutPolynomialSeed", a, d, A, t), Eq,
                        Call("If", Call("LessEqual", t, Call("exp", a)),
                            Call("SumRange", d, Call("mul", Call("apply", A, F.Id("j")),
                                Call("pow", t, Call("mul", D(2), F.Id("j"))))), D(0))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The seed is zero above exp(a). It is not an unknown prolate or Weil eigenfunction."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("polynomial-window-agreement"),
                    DeclarationHandle.Create(Owner + "polynomial_window_agreement"), H("Agreement with the existing canonical polynomial model"),
                    StatementSource.FromAuthor(Disp(Seq(Call("NotEqual", x, Seq(Minus, a)), Rightarrow, Sp,
                        Call("windowMellinSum", a, M, Call("cutPolynomialSeed", a, d, A), x), Eq,
                        Call("polynomialMellinWindow", a, M, d, A, x)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The proof uses the existing mellin_monomial_polynomial_value. "
                        + "The cutoff m*exp(x)<=exp(a) is exactly x<=a-log(m). "
                        + "The half-density and every monomial agree. Only the earlier lower "
                        + "endpoint convention is excluded; the represented L2 functions agree."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("prime-forward-mellin-identity"),
                    DeclarationHandle.Create(Owner + "prime_forward_mellin_identity"), H("Exact all-scale arithmetic intertwining"),
                    StatementSource.FromAuthor(Disp(Seq(hypotheses, Rightarrow, Sp,
                        Call("primeForward", a, M, p, x), Eq,
                        Seq(Call("apply", q, x), Minus, Call("mul", x, Call("apply", p, x)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Assume exp(2a)<=M and h(t)=0 whenever t>exp(a). For every real x, "
                            + "the equality is B_plus E(h)=E(log(t)*h)-X E(h). Inside the window "
                            + "the half-density cancels sqrt(n) exactly. Terms with n*m>M vanish "
                            + "by support. Regroup the remaining product pairs by k=n*m and "
                            + "use the existing sum_{d|k} Lambda(d)=log(k). Outside the window "
                            + "both compressed sides vanish. No parity, positivity, regularity, "
                            + "spectral gap or desired residual identity is assumed."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("prime-even-mellin-identity"),
                    DeclarationHandle.Create(Owner + "prime_even_mellin_identity"), H("Full prime action after evenization"),
                    StatementSource.FromAuthor(Disp(Seq(hypotheses, Rightarrow, Sp,
                        Call("primeSymmetric", a, M, Call("EvenPart", p), x), Eq,
                        Seq(Call("apply", q, x), Plus, Call("apply", q, Seq(Minus, x)), Minus,
                            Call("mul", D(2), x, Call("apply", r, x)), Minus,
                            Call("primeForward", a, M, r, x), Minus,
                            Call("primeForward", a, M, r, Seq(Minus, x)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Here r=(p-Rp)/2 is the actual odd part. Finite prolate arithmetic "
                        + "models need not have r=0. The identity retains its coordinate and "
                        + "translation corrections and all complex phases. For a>=0, the "
                        + "paper L2 consequence bounds this correction by "
                        + "2*(a+sum Lambda(n)/sqrt(n))*norm(r). This bound requires the "
                        + "actual L2 realization and does not claim a sufficiently small "
                        + "Weil residual along an unbounded scale sequence. The source analysis "
                        + "records the independently checked fixed-prolate parity budget."))),
                    DescribeRole.Theorem))));
    }
}
