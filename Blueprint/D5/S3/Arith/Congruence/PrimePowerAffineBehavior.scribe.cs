using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PrimePowerAffineBehaviorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/PrimePowerAffineBehavior.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        Seq(V(name), Open, Join(args), Close);
    private static Formula Join(Formula[] args)
    {
        Formula result = args[0];
        for (int i = 1; i < args.Length; i++) result = Seq(result, Comma, Sp, args[i]);
        return result;
    }
    private static Formula Pow(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Conj(Formula x, Formula y) => Seq(x, Sp, Land, Sp, y);
    private static Formula All(Formula vars, Formula body) => Seq(Open, Forall, Sp, vars, Comma, Sp, body, Close);
    private static Formula Some(Formula vars, Formula body) => Seq(Open, Exists, Sp, vars, Comma, Sp, body, Close);
    private static Formula Imp(Formula x, Formula y) => Seq(Open, x, Sp, Rightarrow, Sp, y, Close);
    private static Formula IffOf(Formula x, Formula y) => Seq(Open, x, Sp, Iff, Sp, y, Close);
    private static Formula Cong(Formula x, Formula y) => Seq(x, Sp, Equiv, Sp, y, Sp,
        Open, Operatorname, Grp(V("mod")), Sp, V("N"), Close);
    private static Formula R(Formula x) => Call("r", x);
    private static Formula E(Formula x) => Call("E", x);
    private static Formula Aff(Formula a, Formula b, Formula x) => Seq(a, x, Plus, V("D"), b);
    private static Formula Pos(Formula a) => Seq(a, Sp, Gt, Sp, D(0));
    private static Formula Nonneg(Formula a) => Seq(a, Sp, Geq, Sp, D(0));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tagged low quotient or high quotient class records exactly the prime-power depth "
            + "responses to all positive multiplications and forward translations.",
        H("Prime-Power Affine Behavior"),
        Blocks(
            Definition("depth", "Saturated prime depth",
                "For natural p,h and integer x, depth(p,h,x) is log base p of gcd(x,p^h). "
                    + "At prime p the theorem identifies it with min(v_p(x),h) for x!=0, "
                    + "and assigns depth h to every zero residue modulo p^h."),
            Describe.Lean(DescribeId.Create("prime-power-affine-depth-data"),
                DeclarationHandle.Create(Prefix + "depth_data"), H("Exact saturated-depth data"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prime p, natural h and integer x, "
                    + "depth(p,h,x)<=h and gcd(x,p^h)=p^depth(p,h,x)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-power-affine-depth-divisibility"),
                DeclarationHandle.Create(Prefix + "depth_divisibility"), H("Depth thresholds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prime p, natural h,j and integer x, "
                    + "p^j divides x and j<=h if and only if j<=depth(p,h,x)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-power-affine-normalized-gcd"),
                DeclarationHandle.Create(Prefix + "normalized_gcd"), H("Normalized gcd"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prime p, natural h and integer x, "
                    + "put r=depth(p,h,x). The gcd of x/p^r and p^(h-r) is one. "
                    + "The division removes their exact common gcd, including the zero residue."))),
                DescribeRole.Theorem),
            Definition("eta", "Disjoint quotient coordinates",
                "Put N=p^h, D=p^e and M=p^(h-e). Write r(x)=depth(p,h,x). "
                    + "The coordinate E(x)=eta(p,h,e,x) is S(r(x),[x/p^r(x)]_M) when r(x)<e, "
                    + "and D([x/p^e]_M) otherwise. The S and D labels are disjoint constructors. "
                    + "The ambient carrier is (natural numbers x ZMod M) disjoint-union ZMod M; "
                    + "the low residue is proved to be a unit, rather than imposed as a restriction "
                    + "on integer source values. Integer division is exact in the relevant branch."),
            Definition("run", "Finite forward continuations",
                "A word is any finite list whose entries are either a positive natural multiplier "
                    + "or a unit marker meaning add p^e. T(w,x)=run(p,e,w,x) applies entries in list "
                    + "order. The empty word returns x. There is no fixed bound on word length."),
            Describe.Lean(DescribeId.Create("prime-power-affine-local-classification"),
                DeclarationHandle.Create(Prefix + "local_classification"),
                H("Exact local classification and its bridges"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The formula uses natural p,h,e with p prime and e<=h. "
                        + "It includes h=0; the positive-depth case takes h>=1. N,D,M,r,E,T have "
                        + "the meanings above. Unless a natural domain is displayed, x,y,X,a,b,A,B "
                        + "are integers. Words w range over all finite continuations. "
                        + "U_M denotes the unit group of ZMod M. Every clause below belongs to "
                        + "the same theorem; there are no additional arithmetic hypotheses.")),
                    Paragraph(Text("Equal coordinates give equal depths after every common legal "
                        + "continuation, and equal responses force equal coordinates. In the low "
                        + "branch the actual quotients x/p^r and y/p^r are units modulo p^(h-r). "
                        + "A Bezout inverse of the first quotient gives a unit t carrying x to y "
                        + "modulo N and satisfying t=1 modulo M. Multiplying each affine response "
                        + "by t preserves its gcd with N. In the high branch coordinate equality "
                        + "already gives full congruence modulo N.")),
                    Paragraph(Text("For the reverse implication, the empty continuation identifies "
                        + "the current depth. Put q=min(r,e), use multiplier p^(e-q), and cancel "
                        + "x by the signed translation parameter -x/p^q. The x-response is zero, "
                        + "so the y-response must be divisible by N. Cancellation leaves equality "
                        + "of the relevant quotient coordinates modulo M. Signed tests have common "
                        + "legal lifts: A=a mod N+N>0 and B=b mod M>=0. Thus the cancellation test "
                        + "is realized by a positive multiplier and finitely many forward additions.")),
                    Paragraph(Text("Every source residue has the positive representative x mod N+N. "
                        + "In particular the zero multiplier residue has representative N, and a "
                        + "zero source residue has a positive representative. At e=h the stored low "
                        + "unit coordinate is 0 modulo 1, the unique unit of that ring; the inverse "
                        + "used in the proof remains an inverse of the actual quotient modulo "
                        + "p^(h-r). These claims concern one local prime power. They do not assemble "
                        + "different primes or realize translations from a separate addend library."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create("prime-power-affine-" + declaration),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ResultFormula()
    {
        Formula p = V("p"), h = V("h"), e = V("e"), x = V("x"), y = V("y"),
            a = V("a"), b = V("b"), aa = V("A"), bb = V("B"), w = V("w");
        Formula quotient = Seq(OpenBracket, x, Slash, Pow(p, R(x)), CloseBracket, Underscore, Grp(V("M")));
        Formula setting = Seq(p, Sp, F.Text, Grp(V("prime")), Comma, Sp,
            h, Comma, e, Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp,
            e, Sp, Leq, Sp, h, Sp, Rightarrow);
        Formula depth = All(x, Conj(Seq(R(x), Sp, Leq, Sp, h),
            Conj(Equal(Call("gcd", x, V("N")), Pow(p, R(x))),
            Conj(IffOf(Equal(R(x), h), Seq(V("N"), Sp, Mid, Sp, x)),
            Conj(Imp(Seq(x, Sp, Neq, Sp, D(0)), Equal(R(x),
                Call("min", Call("v", p, x), h))),
            Imp(Seq(R(x), Sp, Lt, Sp, e), Call("IsUnit", quotient)))))));
        Formula invariant = All(Seq(x, Comma, y), Imp(Cong(x, y),
            Conj(Equal(R(x), R(y)), Equal(E(x), E(y)))));
        Formula lifts = All(x, Some(V("X"), Conj(Pos(V("X")), Cong(x, V("X")))));
        Formula tests = All(Seq(a, Comma, b), Some(Seq(aa, Comma, bb),
            Conj(Pos(aa), Conj(Nonneg(bb), All(x, Cong(Aff(a, b, x), Aff(aa, bb, x)))))));
        Formula naturals = Seq(aa, Comma, bb, Sp, InMacro, Sp, Mathbb, Grp(V("N")));
        Formula normalize = All(w, Some(naturals, Conj(Pos(aa),
            All(x, Equal(Call("T", w, x), Aff(aa, bb, x))))));
        Formula realize = All(naturals, Imp(Pos(aa), Some(w,
            All(x, Equal(Call("T", w, x), Aff(aa, bb, x))))));
        Formula behavior = All(Seq(x, Comma, y), Conj(
            IffOf(Equal(E(x), E(y)), All(Seq(a, Comma, b), Imp(Conj(Pos(a), Nonneg(b)),
                Equal(R(Aff(a, b, x)), R(Aff(a, b, y)))))),
            IffOf(Equal(E(x), E(y)), All(w, Equal(R(Call("T", w, x)), R(Call("T", w, y)))))));
        Formula singleton = Imp(Equal(e, h), All(Seq(V("u"), Comma, V("v"), Sp,
            InMacro, Sp, V("U"), Underscore, Grp(V("M"))), Equal(V("u"), V("v"))));
        return Disp(Seq(setting, RowBreak, Grp(), depth, Sp, Land, RowBreak, Grp(),
            invariant, Sp, Land, RowBreak, Grp(), lifts, Sp, Land, RowBreak, Grp(),
            tests, Sp, Land, RowBreak, Grp(), normalize, Sp, Land, RowBreak, Grp(),
            realize, Sp, Land, RowBreak, Grp(), behavior, Sp, Land, RowBreak, Grp(), singleton));
    }
}
