using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PeriodicTemperleyLiebSeedProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/PeriodicTemperleyLiebSeedProduct.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/ikhlefmorinduchesne2024fusion");
    private const string COne = "Conjecture C.1 (p. 62): \"For p ⩾ 1, the function X^{(p)}_m(ω, x, y) specialised to y = εq^m evaluates to X^{(p)}_m(ω, x, εq^m) = (ωx)^{p−m} ∏_{r=−(m−p−1)/2}^{(m−p−1)/2} (xq^{2r} + εω)(εq^{2r} + xω). (C.5)\"";
    private const string CTwo = "Conjecture C.2 (p. 65): \"The intermediate seed states σ^{(0)}_{0,m}(w, x, y) specialised to y = εq^m evaluate to σ^{(0)}_{0,m}(w, x, εq^m) = (wx)^{−m} ∏_{r=−(m−1)/2}^{(m−1)/2} (xq^{2r} + εw)(εq^{2r} + xw). (C.26)\"";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform product evaluations of the periodic Temperley–Lieb seed recurrences.",
        H("Ikhlef–Morin-Duchesne seed products"),
        Blocks(
            Node("q-number", "The q-number", "qbr", QbrFormula(),
                "Equation (2.14), p. 11, writes [k] = (q^k − q^{−k})/(q − q^{−1}). Here k is an integer and q is complex; all divisions are complex divisions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("q-symmetric-power", "The symmetric q-power", "qcb", QcbFormula(),
                "Proposition C.1 (p. 61): \"where α_p = q^p + q^{−p} and {m} = q^m + q^{−m}.\" The argument k ranges over the integers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("inverse-sum", "A variable and its inverse", "al", AlFormula(),
                "Proposition C.1 (p. 61): \"where X^{(p)}_m(ω, x, y) is a polynomial in the variables α_a = x + x^{−1}, α_b = y + y^{−1} and α_ω = ω + ω^{−1}, that satisfies the recursion relation for m ⩾ p + 1\". The function al sends z to z + z⁻¹.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seed-x", "The positive-depth seed recurrence", "seedX", SeedFormula(false),
                "Proposition C.1 (p. 61): \"where X^{(p)}_m(ω, x, y) is a polynomial in the variables α_a = x + x^{−1}, α_b = y + y^{−1} and α_ω = ω + ω^{−1}, that satisfies the recursion relation for m ⩾ p + 1\". Equations (C.3)–(C.4) give X_{m+1} = (α_a + α_pα_bα_ω/({m}{m+1})) X_m + (α_p² − {m}²)(α_b² − {m}²)(α_ω² − {m}²)/((q − q⁻¹)²[2m − 1][2m + 1]{m}²) X_{m−1}, with X_p = 1 and X_{p+1} = α_a + α_bα_ω/{p + 1}. The expression seedX q x y w p n denotes X^{(p)}_{p+n}(w,x,y). The recurrence index is k = p+n+1; Int.ofNat displays each natural-to-integer coercion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seed-sigma", "The zero-depth seed recurrence", "seedSigma", SeedFormula(true),
                "Proposition C.2 (p. 65): \"The seed states σ^{(0)}_{0,m} with m ⩾ 0 are polynomials in α_a = x + x^{−1}, α_b = y + y^{−1} and α_{ab} = w + w^{−1} that satisfy the linear system for m ⩾ 1\". Equations (C.24)–(C.25) give the displayed recurrence and its two initial values, independently of seedX.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seed-product", "The symmetric finite product", "seedProduct", ProductFormula(),
                COne + " The product has N factors, with integer exponent 2r = −N+1+2j for j in Finset.range N. For N=0 the product is empty and equals one. The same expression occurs in (C.26).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seed-product-claim", "Conjectures C.1 and C.2", "claim",
                Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                COne + " " + CTwo + " The domain is nonzero complex q,x,w, with q not a root of unity and ε equal to 1 or −1. The first assertion has 1 ≤ p ≤ m; the second has every natural m. Natural subtraction m−p is truncated subtraction, and agrees with the integer difference under p ≤ m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("seed-product-result", "Both product formulas hold", "result", Disp(ClaimBody()),
                "The seed recurrence equals a monic Askey–Wilson recurrence after Q=q², h=q^(p+1), a=h/(yw), b=hw/y, c=hyw, d=hy/w, and T=−al(x). A coupled Darboux identity shifts a to aQ. At the terminal degree the coefficient A vanishes because abQ^(N−1)=1. Induction then gives one linear factor at each shift. Symmetric exponents sum to zero, producing seedProduct. The separately defined sigma recurrence equals the p=0 seedX recurrence. The formulas hold uniformly in m and p; intermediate values at a fixed specialization are not asserted to factor.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ikhlef-morin-duchesne-2023-conjectures-c1-c2"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Cast(Formula value) => Seq(Qualified("Int", "ofNat"), Parenthesized(value));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Sub(Formula left, Formula right) => Seq(left, Sp, Minus, Sp, right);
    private static Formula Negate(Formula value) => Seq(Minus, value);
    private static Formula Mul(params Formula[] values)
    {
        Formula result = values[0];
        for (int i = 1; i < values.Length; i++) result = Seq(result, Sp, Cdot, Sp, values[i]);
        return result;
    }
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Square(Formula value) => Power(value, D(2));
    private static Formula Inverse(Formula value) => Power(value, Negate(D(1)));
    private static Formula Fraction(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula Nonzero(Formula value) => Seq(value, Sp, Neq, Sp, D(0));
    private static Formula Le(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Alpha(Formula value) => Call("al", value);
    private static Formula Qcb(Formula q, Formula value) => Call("qcb", q, value);
    private static Formula Qbr(Formula q, Formula value) => Call("qbr", q, value);

    private static Formula QbrFormula() => Disp(All("q", Complex(), All("k", Int(),
        Equal(Qbr(V("q"), V("k")), Fraction(
            Sub(Power(V("q"), V("k")), Power(V("q"), Negate(V("k")))),
            Sub(V("q"), Inverse(V("q"))))))));
    private static Formula QcbFormula() => Disp(All("q", Complex(), All("k", Int(),
        Equal(Qcb(V("q"), V("k")), Add(Power(V("q"), V("k")), Power(V("q"), Negate(V("k"))))))));
    private static Formula AlFormula() => Disp(All("z", Complex(),
        Equal(Alpha(V("z")), Add(V("z"), Inverse(V("z"))))));

    private static Formula SeedFormula(bool sigma)
    {
        Formula q=V("q"), x=V("x"), y=V("y"), w=V("w"), p=V("p"), n=V("n"), k=V("k");
        Formula Value(Formula index) => sigma ? Call("seedSigma",q,x,y,w,index) : Call("seedX",q,x,y,w,p,index);
        Formula b = Mul(Alpha(y), Alpha(w));
        Formula init = Add(Alpha(x), Fraction(b, Qcb(q, sigma ? D(1) : Add(Cast(p),D(1)))));
        Formula diag = Add(Alpha(x), Fraction(Mul(sigma ? D(2) : Alpha(Power(q,p)),b),
            Mul(Qcb(q,k), Qcb(q,Add(k,D(1))))));
        Formula second = Sub(Square(Alpha(y)), Square(Qcb(q,k)));
        Formula third = Sub(Square(Alpha(w)), Square(Qcb(q,k)));
        Formula off = sigma
            ? Fraction(Mul(Square(Qbr(q,k)), Parenthesized(second), Parenthesized(third)),
                Mul(Qbr(q,Add(Mul(D(2),k),D(1))), Qbr(q,Sub(Mul(D(2),k),D(1))), Square(Qcb(q,k))))
            : Fraction(Mul(Parenthesized(Sub(Square(Alpha(Power(q,p))), Square(Qcb(q,k)))),
                    Parenthesized(second), Parenthesized(third)),
                Mul(Square(Parenthesized(Sub(q,Inverse(q)))), Qbr(q,Sub(Mul(D(2),k),D(1))),
                    Qbr(q,Add(Mul(D(2),k),D(1))), Square(Qcb(q,k))));
        Formula firstTerm = Mul(Parenthesized(diag), Value(Add(n,D(1))));
        Formula otherTerm = Mul(off, Value(n));
        Formula step = Seq(Operatorname, Grp(V("let")), Sp, k, Colon, Sp, Int(), Sp, Colon, Eq, Sp,
            sigma ? Add(Cast(n),D(1)) : Add(Add(Cast(p),Cast(n)),D(1)), Semi, Sp,
            Equal(Value(Add(n,D(2))), sigma ? Sub(firstTerm,otherTerm) : Add(firstTerm,otherTerm)));
        Formula body = And(Equal(Value(D(0)),D(1)), And(Equal(Value(D(1)),init), All("n",Nat(),step)));
        if (!sigma) body=All("p",Nat(),body);
        return Disp(All("q",Complex(),All("x",Complex(),All("y",Complex(),All("w",Complex(),body)))));
    }

    private static Formula ProductFormula()
    {
        Formula q=V("q"), x=V("x"), w=V("w"), e=V("epsilon"), n=V("N"), j=V("j");
        Formula exponent=Add(Add(Negate(Cast(n)),D(1)),Mul(D(2),Cast(j)));
        Formula power=Power(q,exponent);
        Formula factor=Mul(Parenthesized(Add(Mul(x,power),Mul(e,w))),
            Parenthesized(Add(Mul(e,power),Mul(x,w))));
        Formula product=Seq(Prod,Underscore,Grp(Seq(j,Sp,InMacro,Sp,Qualified("Finset","range"),Parenthesized(n))),Sp,Parenthesized(factor));
        Formula body=Equal(Call("seedProduct",q,x,w,e,n),Mul(Power(Parenthesized(Mul(w,x)),Negate(Cast(n))),product));
        return Disp(All("q",Complex(),All("x",Complex(),All("w",Complex(),All("epsilon",Complex(),All("N",Nat(),body))))));
    }

    private static Formula ClaimBody()
    {
        Formula q=V("q"), x=V("x"), w=V("w"), e=V("epsilon"), p=V("p"), m=V("m"), n=V("n");
        Formula nonroot=All("n",Nat(),Imp(Le(D(1),n),Seq(Power(q,n),Sp,Neq,Sp,D(1))));
        Formula sign=Seq(Equal(e,D(1)),Sp,Lor,Sp,Equal(e,Negate(D(1))));
        Formula cOne=All("p",Nat(),All("m",Nat(),Imp(Le(D(1),p),Imp(Le(p,m),
            Equal(Call("seedX",q,x,Mul(e,Power(q,m)),w,p,Sub(m,p)),Call("seedProduct",q,x,w,e,Sub(m,p)))))));
        Formula cTwo=All("m",Nat(),Equal(Call("seedSigma",q,x,Mul(e,Power(q,m)),w,m),Call("seedProduct",q,x,w,e,m)));
        return All("q",Complex(),All("x",Complex(),All("w",Complex(),All("epsilon",Complex(),
            Imp(Nonzero(q),Imp(Nonzero(x),Imp(Nonzero(w),Imp(nonroot,Imp(sign,And(cOne,cTwo))))))))));
    }
}
