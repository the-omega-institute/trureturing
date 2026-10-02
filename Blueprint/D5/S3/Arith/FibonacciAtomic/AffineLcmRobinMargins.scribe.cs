using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class AffineLcmRobinMarginsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/AffineLcmRobinMargins.";
    private const string CorePrefix = "D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two actual affine lcm families have positive Robin margins and an unbounded weight gap under explicit analytic premises.",
        H("Affine Lcm Robin Margins"),
        Blocks(
            Node("affine-seed-lcm", "Actual affine seed lcm", "affineLcm",
                Disp(Equal(Q, Seq(new Formula.Subscript(Call("lcm"),
                    Seq(D(0), Le, Sp, F.Id("a"), Lt, L)), Par(Seq(D(3), F.Id("a"), Plus, D(5)))))),
                "Q(L) is the finite lcm of the natural seeds 3a+5 for 0<=a<L. The empty lcm is one.",
                DescribeRole.Definition),
            Node("saturated-affine-core", "Saturated core", "saturatedCore",
                Disp(Equal(A, Seq(Pow(D(3), Call("NatLog", D(3), L)), Q))),
                "A(L)=3^(Nat.log 3 L)*Q(L). For positive L the natural logarithmic exponent agrees with the natural floor of log(L)/log(3).",
                DescribeRole.Definition),
            Node("full-short-signature", "Full short signature", "shortSignature",
                Disp(Equal(Call("O", L, N), Par(Seq(Call("v", D(3), N), Comma, Call("gcdVector", L, N))))),
                "O(L,N) retains v_3(N) and the function a:Fin L -> gcd(N,3a+5), so every sampled gcd coordinate remains visible.",
                DescribeRole.Definition),
            Node("visible-divisor-core", "Visible divisor core", "visibleCore",
                Disp(Equal(Call("B", L, N), Seq(Pow(D(3), Call("v", D(3), N)), Call("gcd", N, Q)))),
                "B(L,N)=3^v_3(N)*gcd(N,Q(L)). Prime valuations use natural factorization; the exact fiber assertion is restricted to positive N.",
                DescribeRole.Definition),
            Node("actual-residue-theta", "Residue prime logarithmic sum", "residueTheta",
                Disp(Equal(Call("theta", F.Id("r"), F.Id("y")), Seq(new Formula.Subscript(Sum,
                    Seq(Call("Prime", F.Id("p")), Comma, F.Id("p"), Le, Sp, F.Id("y"), Comma,
                        Equal(Call("mod", F.Id("p"), D(3)), F.Id("r")))), Log(F.Id("p"))))),
                "theta(r,y) sums log(p) over primes p<=floor(y) with p mod 3=r. The natural floor convention makes the sum empty at negative cutoffs.",
                DescribeRole.Definition),
            Node("normalized-robin-margin", "Robin margin", "robinMargin",
                Disp(Equal(Delta(N), Sub(Seq(E, Log(Log(N))), U(N)))),
                "Delta(N)=exp(gamma)*log(log(N))-sigma(N)/N. The intended Robin domain is N>1; the theorem eventually gives N>5040.",
                DescribeRole.Definition),
            Node("actual-affine-robin-margins", "Two positive margins in one actual signature fiber", "result",
                ResultFormula(),
                "Fix any real C>0, without requiring C>1. Assume theta(r,y)=y/2+O(y/log(y)^3) for each r=1,2 and the additive premise P(y)-exp(gamma)*log(y)->0. Here P is the complete inverse Euler product over primes at most y. Along all natural L tending to infinity, put m=3L+2, x=(C/256)*m*log(m), T=product(m<p<=x) p and H=A(L)*T. The displayed size and weight limits hold with E=exp(gamma). Both explicit margin constants are positive. Both normalized contrast rates tend to one, and U(H)-U(A) tends to positive infinity.",
                DescribeRole.Theorem),
            Paragraph(Text(
                "For every L>=2, Q and A are positive, 3 does not divide Q, v_3(A)=Nat.log 3 L, D_L divides A which divides D_m, and B(L,A)=A. The prime support and positive-N fiber identities below hold for every such L, and 5040 divides A whenever L>=16. The eventual context holds simultaneously: A and H are positive, exceed 5040, are divisible by 5040, satisfy U(N)<E*log(log(N)), and are at most exp(C*L*log(L)). Their full short signatures agree, B(L,A)=B(L,H)=A, and A is coprime to T. Also 3 does not divide Q, v_3(A)=Nat.log 3 L, and D_L divides A, which divides D_m, where D_j=lcm(1,...,j). For every prime p, p divides Q exactly when (p mod 3=1 and 2p<=m) or (p mod 3=2 and p<=m). For every positive N, O(L,N)=O(L,A) exactly when N=A*t for a natural t>=1 coprime to 3; every such N has visible core A.")),
            Paragraph(Text(
                "The proof uses the actual affine prime-power occurrence witnesses, including the seed 8 for the prime power 2. Abel summation controls the missing residue-one band m/2<p<=m. The same band and valuation defect enter both exact Euler identities. The additive product premise supplies the constant terms. The intermediate affine lcm size asymptotic is classical; see Qian and Hong, arXiv:1204.5415v2, Corollary 1.2 with a=3,b=2,l=1,m=0. The conclusions concern these two specified families under the stated premises and do not classify Robin truth on the whole fiber.")))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Handle(declaration)), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static string Handle(string declaration) => declaration switch
    {
        "affineLcm" or "saturatedCore" or "shortSignature" or "visibleCore" or
        "residueTheta" or "robinMargin" => CorePrefix + declaration,
        _ => Prefix + declaration
    };

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Log(Formula a) => Call("log", a);
    private static Formula U(Formula a) => Call("U", a);
    private static Formula Delta(Formula a) => Call("Delta", a);
    private static Formula L => F.Id("L");
    private static Formula N => F.Id("N");
    private static Formula C => F.Id("C");
    private static Formula M => F.Id("m");
    private static Formula X => F.Id("x");
    private static Formula E => F.Id("E");
    private static Formula Q => Call("Q", L);
    private static Formula A => Call("A", L);
    private static Formula HN => Call("H", L);
    private static Formula Limit(Formula f, Formula value) =>
        Equal(Seq(new Formula.Subscript(Lim, Seq(L, To, Infty)), Par(f)), value);
    private static Formula And(params Formula[] fields)
    {
        var result = fields[0];
        for (var i = 1; i < fields.Length; i++) result = Seq(result, Land, Sp, fields[i]);
        return result;
    }
    private static Formula ResultFormula()
    {
        var halfLogTwo = Fr(Log(D(2)), D(2));
        var coreConstant = Seq(E, Log(Fr(D(3), Seq(D(2), Call("sqrt", D(2))))));
        var highConstant = Seq(Fr(E, D(2)), Log(D(2)));
        var gap = Sub(U(HN), U(A));
        var threshold = new Formula.Subscript(L, D(0));
        return Disp(Seq(Forall, Sp, C, InMacro, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma, Sp,
            D(0), Lt, C, Land, Sp, Call("Hypothesis3021"), Rightarrow, Sp,
            Par(And(
                Par(Seq(Forall, Sp, L, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
                    D(2), Le, Sp, L, Rightarrow, Sp, Call("ArithmeticContext", L))),
                Limit(Fr(Log(A), Seq(Fr(D(3), D(4)), M)), D(1)),
                Limit(Fr(Log(A), Seq(Fr(D(9), D(4)), L)), D(1)),
                Limit(Sub(U(A), Seq(E, Par(Sub(Log(M), halfLogTwo)))), D(0)),
                Limit(Delta(A), coreConstant), Seq(D(0), Lt, coreConstant),
                Limit(Fr(Log(HN), X), D(1)),
                Limit(Sub(U(HN), Seq(E, Par(Sub(Log(X), halfLogTwo)))), D(0)),
                Limit(Delta(HN), highConstant), Seq(D(0), Lt, highConstant),
                Limit(Seq(Par(Sub(Fr(U(HN), U(A)), D(1))), Fr(Log(L), Log(Log(L)))), D(1)),
                Limit(Fr(gap, Seq(E, Log(Log(L)))), D(1)),
                Limit(gap, Infty),
                Par(Seq(Exists, Sp, threshold, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
                    Forall, Sp, L, InMacro, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
                    threshold, Le, Sp, L, Rightarrow, Sp, Call("EventualContext", C, L, A, HN)))))));
    }
}
