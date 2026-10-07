using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class StrongDivisibilityLcmMertensDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef ReconstructionSource =
        LibraryNoteRef.Create("D5/L/Factorization/nowicki2013strongdivisibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive strong divisibility sequence has an exact prefix-lcm logarithm as a Mertens dilation at every natural cutoff.",
        H("Strong Divisibility and the Prefix Lcm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-prefix-lcm-mertens-dilation"),
                DeclarationHandle.Create("D5/S3/Arith/StrongDivisibilityLcmMertens.log_prefix_lcm_eq_mertens_dilation"),
                H("Exact logarithmic Mertens dilation"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(ReconstructionSource),
                Blocks(
                    Paragraph(Text("Let u map natural numbers to natural numbers. Assume u(n)>0 for every n>0, "
                        + "and gcd(u(a),u(b))=u(gcd(a,b)) whenever a,b>0. The value u(0) is arbitrary, "
                        + "and u(1) may be any positive integer. Put L(N)=lcm{u(d):0<d<=N}, with L(0)=1, "
                        + "and M(t)=sum_{0<m<=t} mu(m), where mu is the ordinary Moebius function. "
                        + "For every natural N>=0, the displayed identity holds. All quotients N/d in the "
                        + "cutoff are natural division; every supported d is positive.")),
                    Paragraph(Text("The proof constructs the positive natural quotient A(n)=L(n)/L(n-1), "
                        + "for n>0, using exact divisibility of consecutive prefix lcms. Its live induction "
                        + "proves gcd(u(n),L(K))=product_{0<d<=K,d|n} A(d), simultaneously for every n>0. "
                        + "When K+1 does not divide n, the positive index gcd(n,K+1) is at most K; "
                        + "its u-value is already in the previous prefix and the gcd does not increase. "
                        + "When K+1 divides n, strong divisibility gives u(K+1)|u(n). Gcd/lcm "
                        + "distributivity, the gcd-times-lcm identity and cancellation of positive natural "
                        + "factors show that the gcd acquires exactly the factor A(K+1). The distributor "
                        + "is reused from its original repository source, FiniteCompatibleCrt.")),
                    Paragraph(Text("At K=n, the projection reconstructs u(n)=product_{d|n} A(d). "
                        + "A separate telescope gives L(N)=product_{0<d<=N} A(d), including N=0. "
                        + "Taking logarithms of positive finite products and applying Mathlib's additive "
                        + "Moebius inversion gives log A(n)=(mu*logU)(n) for n>0. The arithmetic function "
                        + "logU is defined to vanish at zero and equals log u(n) for positive n, so no "
                        + "hypothesis on u(0) enters. Mathlib's finite summatory Dirichlet convolution "
                        + "identity then yields the exact dilation formula.")),
                    Paragraph(Text("Nowicki's Strong divisibility and lcm-sequences, Theorem 2.1, PDF p. 4, "
                        + "attests the classical divisor reconstruction from successive prefix-lcm "
                        + "quotients in a gcd-domain, with equalities up to units. Positive natural values "
                        + "remove unit ambiguity. The logarithmic Mertens formula is a classical "
                        + "consequence of that reconstruction and Moebius inversion; the paper does not "
                        + "literally display this formula. The projection induction is independently "
                        + "implemented in Lean here. No mathematical originality or resolution of the "
                        + "remaining Robin or Riemann-hypothesis problem is claimed.")),
                    Paragraph(Text("For N=0 both sides are zero. For N=1 the formula is log u(1)=log u(1), "
                        + "so it preserves a positive nonunit first value. The actual identity sequence "
                        + "and the literal Fibonacci sequence are applications of this generic theorem; "
                        + "they do not add retained public wrappers to this module."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var u = F.Id("u"); var n = F.Id("n"); var a = F.Id("a");
        var b = F.Id("b"); var d = F.Id("d"); var m = F.Id("m"); var N = F.Id("N");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula cutoff(Formula index, Formula upper) => Seq(D(0), Lt, Sp, index, Le, Sp, upper);
        Formula logU(Formula index) => Call("log", Call("u", index));
        Formula strong = Seq(Forall, Sp, a, Comma, b, InMacro, Sp, nat, Comma, Sp,
            D(0), Lt, Sp, a, Land, Sp, D(0), Lt, Sp, b, Rightarrow, Sp,
            Call("gcd", Seq(Call("u", a), Comma, Sp, Call("u", b))), Eq, Sp,
            Call("u", Call("gcd", Seq(a, Comma, Sp, b))));
        Formula positivity = Seq(Forall, Sp, n, InMacro, Sp, nat, Comma, Sp,
            D(0), Lt, Sp, n, Rightarrow, Sp, D(0), Lt, Sp, Call("u", n));
        Formula quotient = Seq(Lfloor, new Formula.Fraction(N, d), Rfloor);
        Formula inner = Seq(new Formula.Subscript(Sum, cutoff(m, quotient)), Call("mu", m));
        Formula outer = Seq(new Formula.Subscript(Sum, cutoff(d, N)), logU(d), inner);
        return Disp(Seq(Forall, Sp, u, Colon, Sp, new Formula.TypeArrow(nat, nat), Comma, Sp,
            Open, Open, positivity, Close, Land, Sp, Open, strong, Close, Close, Rightarrow, Sp,
            Forall, Sp, N, InMacro, Sp, nat, Comma, Sp,
            Call("log", Call("L", N)), Eq, Sp, outer));
    }
}
