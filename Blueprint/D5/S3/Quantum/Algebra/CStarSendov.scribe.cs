using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.CStarSendovFormulas;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CStarSendovDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CStarSendov.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical branches exchange over a compact interval and refute C*-algebraic Sendov.",
        H("CStarSendov"), Blocks(
            Node("cstarDisc", "The C*-algebraic disc", DiscFormula(),
                "Definition 2.3, p. 3: “Given a unital C*-algebra 𝒜 with identity 1 and an element a∈𝒜, we define the C*-algebraic closed unit disc centered at a and of radius r>0, r∈ℝ, denoted as 𝔻̅*(a,r) by 𝔻̅*(a,r) ≔ {z∈𝒜: (z−a)(z−a)* ≤ √r·1}.” The scalar √r is embedded in ℂ before acting on A. The encoding defines the expression for every real r; both conjectures use r=1.", DescribeRole.Definition, true),
            Node("IsConvexForm", "Positive barycentric form", ConvexFormula(),
                "Theorem 2.2, Equation (1), p. 2: “there are positive ω_z₁, …, ω_zₙ ∈ 𝒜 such that z=∑_{j=1}ⁿ ω_zⱼ aⱼ, ∑_{j=1}ⁿ ω_zⱼ=1.” Positive means nonnegative in the C*-order. Indices become zero-based Fin n. The constructed weights are also invertible and strictly positive pointwise.", DescribeRole.Definition, true),
            Node("ramp", "The clipped linear ramp", All("t", Real(), Eq(Invoke("ramp", Sym("t")), Clamp(Sym("t")))),
                "The ramp is zero below zero, linear from zero to one, and one above one.", DescribeRole.Definition),
            Node("cx", "The real coordinate of the polygon", All("t", Real(), Eq(Invoke("cx", Sym("t")), Cx())),
                "The real coordinate is piecewise linear, with turns at the integer parameters from zero to six.", DescribeRole.Definition),
            Node("cy", "The imaginary coordinate of the polygon", All("t", Real(), Eq(Invoke("cy", Sym("t")), Cy())),
                "The imaginary coordinate stays positive in the interior of the interval.", DescribeRole.Definition),
            Node("cfun", "The polygon in the complex plane", All("t", Real(), Eq(Invoke("cfun", Sym("t")), Plus(Cast(Invoke("cx", Sym("t")), Complex()), Mul(Cast(Invoke("cy", Sym("t")), Complex()), Invoke("Complex.I"))))),
                "The vertices are −9/10, −1/10+4i/5, 1/10+4i/5, 1/10+9i/10, −1/10+9i/10, −1/10+4i/5, and −9/10.", DescribeRole.Definition),
            Node("c", "The continuous coefficient", All("t", Interval(), Eq(App(Sym("c"), Sym("t")), Invoke("cfun", Cast(Sym("t"), Real())))),
                "The continuous map c is the restriction of cfun to Set.Icc 0 6, with codomain ℂ.", DescribeRole.Definition),
            Node("dfun", "The discriminant expression", All("t", Real(), Eq(Invoke("dfun", Sym("t")), Plus(Pow(Invoke("cfun", Sym("t")), 2), Rat(3, 4, Complex())))),
                "The derivative discriminant is c²+3/4. Its two branch points in the coefficient plane are ±i√3/2.", DescribeRole.Definition),
            Node("rootU", "The real square-root coordinate", All("z", Complex(), Eq(Invoke("rootU", Sym("z")), Invoke("Real.sqrt", Div(Plus(Norm(Sym("z")), Invoke("Complex.re", Sym("z"))), D(2))))),
                "The coordinate is the nonnegative real square root of (|z|+Re z)/2.", DescribeRole.Definition),
            Node("rootV", "The imaginary square-root coordinate", All("z", Complex(), Eq(Invoke("rootV", Sym("z")), Invoke("Real.sqrt", Div(Sub(Norm(Sym("z")), Invoke("Complex.re", Sym("z"))), D(2))))),
                "The coordinate is the nonnegative real square root of (|z|−Re z)/2.", DescribeRole.Definition),
            Node("rootR", "The square-root chart with positive real part", All("z", Complex(), Eq(Invoke("rootR", Sym("z")), Plus(Cast(Invoke("rootU", Sym("z")), Complex()), Mul(Cast(Div(Invoke("Complex.im", Sym("z")), Mul(D(2), Invoke("rootU", Sym("z")))), Complex()), Invoke("Complex.I"))))),
                "On its domain the square of this chart is z.", DescribeRole.Definition),
            Node("rootI", "The square-root chart with positive imaginary part", All("z", Complex(), Eq(Invoke("rootI", Sym("z")), Plus(Cast(Div(Invoke("Complex.im", Sym("z")), Mul(D(2), Invoke("rootV", Sym("z")))), Complex()), Mul(Cast(Invoke("rootV", Sym("z")), Complex()), Invoke("Complex.I"))))),
                "This chart joins the first chart above the real axis and its negative below the real axis.", DescribeRole.Definition),
            Node("sfun", "The square root along the polygon", All("t", Real(), Eq(Invoke("sfun", Sym("t")), Invoke("ite", Le(Sym("t"), D(2)), Invoke("rootR", Invoke("dfun", Sym("t"))), Invoke("ite", Le(Sym("t"), D(4)), Invoke("rootI", Invoke("dfun", Sym("t"))), Negate(Invoke("rootR", Invoke("dfun", Sym("t")))))))),
                "The chart switches occur at t=2 and t=4, where the selected values agree.", DescribeRole.Definition),
            Node("s", "The continuous square root", All("t", Interval(), Eq(App(Sym("s"), Sym("t")), Invoke("sfun", Cast(Sym("t"), Real())))),
                "The continuous map s has square c²+3/4. Its endpoint values are √(39/25) and −√(39/25).", DescribeRole.Definition),
            Node("a", "The three roots", Eq(Cast(Sym("a"), Arr(Fin(D(3)), ContinuousAlgebra())), Tuple(Smul(Rat(1, 2, Complex()), OneAlgebra()), Smul(Negate(Rat(1, 2, Complex())), OneAlgebra()), Sym("c"))),
                "The tuple gives the roots 1/2, −1/2, c in C(Set.Icc 0 6,ℂ).", DescribeRole.Definition),
            Node("bplus", "The first critical branch", Eq(Cast(Sym("bplus"), ContinuousAlgebra()), Smul(Rat(1, 3, Complex()), Plus(Sym("c"), Sym("s")))),
                "This branch starts near the root 1/2 and ends at the distant critical point.", DescribeRole.Definition),
            Node("bminus", "The second critical branch", Eq(Cast(Sym("bminus"), ContinuousAlgebra()), Smul(Rat(1, 3, Complex()), Sub(Sym("c"), Sym("s")))),
                "The second branch starts at the distant critical point and ends near 1/2.", DescribeRole.Definition),
            Node("bs", "The supplied critical-root tuple", Eq(Cast(Sym("bs"), Arr(Fin(D(2)), ContinuousAlgebra())), Tuple(Sym("bplus"), Sym("bminus"))),
                "Both branches are algebra-valued zeros, with positive barycentric representations.", DescribeRole.Definition),
            Node("ordered_deriv_apply", "The cubic derivative at every parameter", All("z", ContinuousAlgebra(), All("t", Interval(), Eq(App(Deriv(Sym("a"), Sym("z")), Sym("t")), Sub(Sub(Mul(Cast(D(3), Complex()), Pow(App(Sym("z"), Sym("t")), 2)), Mul(Mul(Cast(D(2), Complex()), App(Sym("c"), Sym("t"))), App(Sym("z"), Sym("t")))), Rat(1, 4, Complex()))))),
                "Pointwise evaluation of the ordered sum yields 3z²−2cz−1/4.", DescribeRole.Lemma),
            Node("critical_both", "Both branches are critical", And(Eq(Deriv(Sym("a"), Sym("bplus")), D(0)), Eq(Deriv(Sym("a"), Sym("bminus")), D(0))),
                "The factorization 3(z−bplus)(z−bminus) gives both zeros.", DescribeRole.Lemma),
            Node("roots_in_disc", "All polynomial roots are in the disc", All("j", Fin(D(3)), Mem(App(Sym("a"), Sym("j")), Invoke("cstarDisc", D(0), D(1)))),
                "Every polygon vertex has squared norm at most 82/100; the segments remain inside the unit disc.", DescribeRole.Lemma),
            Node("critical_in_disc", "Both critical branches are in the disc", And(Mem(Sym("bplus"), Invoke("cstarDisc", D(0), D(1))), Mem(Sym("bminus"), Invoke("cstarDisc", D(0), D(1)))),
                "The estimates |c|≤1 and |s|≤2 imply that both branches have norm at most one.", DescribeRole.Lemma),
            Node("no_critical_in_half_disc", "No critical zero is close to one half", All("z", ContinuousAlgebra(), Imp(Eq(Deriv(Sym("a"), Sym("z")), D(0)), new Formula.Not(Mem(Sym("z"), Invoke("cstarDisc", Smul(Rat(1, 2, Complex()), OneAlgebra()), D(1)))))),
                "A continuous zero follows one of the two branches on the entire connected interval. The first branch is farther than one from 1/2 at t=6; the second is farther than one at t=0.", DescribeRole.Lemma),
            Node("critical_convex_form", "Positive barycentric representations", All("z", ContinuousAlgebra(), Imp(Eq(Deriv(Sym("a"), Sym("z")), D(0)), Invoke("IsConvexForm", Sym("a"), Sym("z")))),
                "The positive pointwise weights are inverse squared distances, divided by their sum. None of the distances vanishes, so the weights are continuous and invertible.", DescribeRole.Lemma),
            Node("claimSendov", "Krishna's Conjecture 2.5", Iff(Sym("claimSendov"), Claim(false)),
                SourceClaim(false) + " The encoding uses zero-based Fin indices, degrees 2≤n, and unital algebras in Type with PartialOrder and StarOrderedRing. The derivative is the existing orderedDeriv, omitting one factor at a time. The conclusion allows any zero, rather than only the listed b values.", DescribeRole.Definition, true),
            Node("result", "Conjecture 2.5 is false", new Formula.Not(Sym("claimSendov")),
                "The cubic in C(Set.Icc 0 6,ℂ) satisfies all the disc and barycentric hypotheses. The two critical branches exchange between the endpoints, and neither is uniformly within one of the constant root 1/2.", DescribeRole.Theorem, false))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature = false, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

internal static class CStarSendovFormulas
{
    internal static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/krishna2022cstarsendov");
    internal static Formula Sym(string name) => F.Id(name);
    private static Formula Named(string name)
    {
        var parts = name.Split('.');
        var result = Seq(Operatorname, Grp(Sym(parts[0])));
        foreach (var part in parts.Skip(1)) result = Seq(result, Dot, Operatorname, Grp(Sym(part)));
        return result;
    }
    internal static Formula Invoke(string name, params Formula[] args) => args.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. args]);
    internal static Formula App(Formula f, params Formula[] args) => new Formula.Apply(Parenthesized(f), [.. args]);
    internal static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    internal static Formula Typed(Formula value, Formula type) => Seq(Parenthesized(value), Colon, type);
    internal static Formula Cast(Formula value, Formula type) => Parenthesized(Typed(value, type));
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    internal static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    internal static Formula All(string v, Formula type, Formula body) => Seq(Forall, Sp, Sym(v), Colon, type, Comma, Sp, body);
    internal static Formula Exists(string v, Formula type, Formula body) => Seq(F.Exists, Sp, Sym(v), Colon, type, Comma, Sp, body);
    internal static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pow(Formula a, byte n) => new Formula.Power(Parenthesized(a), D(n));
    internal static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    internal static Formula Rat(byte a, byte b, Formula type) => Div(Cast(new Formula.Number(a), type), Cast(new Formula.Number(b), type));
    internal static Formula Negate(Formula a) => new Formula.Negate(Parenthesized(a));
    internal static Formula Norm(Formula a) => new Formula.Norm(a);
    internal static Formula Smul(Formula a, Formula b) => Invoke("SMul.smul", a, b);
    internal static Formula Real() => Seq(Mathbb, Grp(Sym("R")));
    internal static Formula Complex() => Seq(Mathbb, Grp(Sym("C")));
    internal static Formula Nat() => Seq(Mathbb, Grp(Sym("N")));
    internal static Formula Fin(Formula n) => Invoke("Fin", n);
    internal static Formula Interval() => Invoke("Set.Icc", Cast(D(0), Real()), D(6));
    internal static Formula ContinuousAlgebra() => Invoke("C", Interval(), Complex());
    internal static Formula OneAlgebra() => Cast(D(1), ContinuousAlgebra());
    internal static Formula Deriv(Formula a, Formula z) => Invoke("CStarSchoenberg.orderedDeriv", a, z);
    internal static Formula Instances(Formula A, Formula body, params string[] names)
    {
        foreach (var name in names.Reverse()) body = Seq(OpenBracket, Invoke(name, A), CloseBracket, Sp, body);
        return body;
    }
    internal static Formula Tuple(params Formula[] items)
    {
        var result = Seq(Bang, OpenBracket, items[0]);
        foreach (var item in items.Skip(1)) result = Seq(result, Comma, Sp, item);
        return Seq(result, CloseBracket);
    }
    internal static Formula Sum(string v, Formula n, Formula body) => Seq(new Formula.Subscript(F.Sum, Typed(Sym(v), Fin(n))), Parenthesized(body));
    internal static Formula Clamp(Formula t) => Invoke("min", D(1), Invoke("max", D(0), t));
    private static Formula RampCall(Formula t) => Invoke("ramp", t);
    internal static Formula Cx() => Sub(Sub(Plus(Plus(Negate(Rat(9, 10, Real())), Mul(Rat(4, 5, Real()), RampCall(Sym("t")))), Mul(Rat(1, 5, Real()), RampCall(Sub(Sym("t"), D(1))))), Mul(Rat(1, 5, Real()), RampCall(Sub(Sym("t"), D(3))))), Mul(Rat(4, 5, Real()), RampCall(Sub(Sym("t"), D(5)))));
    internal static Formula Cy() => Sub(Sub(Plus(Mul(Rat(4, 5, Real()), RampCall(Sym("t"))), Mul(Rat(1, 10, Real()), RampCall(Sub(Sym("t"), D(2))))), Mul(Rat(1, 10, Real()), RampCall(Sub(Sym("t"), D(4))))), Mul(Rat(4, 5, Real()), RampCall(Sub(Sym("t"), D(5)))));
    internal static Formula DiscFormula()
    {
        var A = Sym("A"); var a = Sym("a"); var r = Sym("r"); var z = Sym("z");
        var predicate = Le(Mul(Sub(z, a), Invoke("star", Sub(z, a))), Smul(Cast(Invoke("Real.sqrt", r), Complex()), Cast(D(1), A)));
        var set = Seq(OpenBrace, z, Colon, A, Mid, predicate, CloseBrace);
        return All("A", Sym("Type"), Instances(A, All("a", A, All("r", Real(), Eq(Invoke("cstarDisc", a, r), set))), "CStarAlgebra", "PartialOrder"));
    }
    internal static Formula ConvexFormula()
    {
        var A = Sym("A"); var n = Sym("n"); var a = Sym("a"); var z = Sym("z"); var w = Sym("w");
        var body = Exists("w", Arr(Fin(n), A), And(All("j", Fin(n), Le(D(0), App(w, Sym("j")))), And(Eq(Sum("j", n, App(w, Sym("j"))), D(1)), Eq(z, Sum("j", n, Mul(App(w, Sym("j")), App(a, Sym("j"))))))));
        return All("A", Sym("Type"), Instances(A, All("n", Nat(), All("a", Arr(Fin(n), A), All("z", A, Iff(Invoke("IsConvexForm", a, z), body)))), "CStarAlgebra", "PartialOrder"));
    }
    internal static Formula Claim(bool commutative)
    {
        var A = Sym("A"); var n = Sym("n"); var a = Sym("a"); var b = Sym("b");
        Formula Zero(Formula z) => commutative ? Invoke("HasCStarDeriv", Invoke("CStarDualMeanValue.orderedPoly", a), z, D(0)) : Eq(Deriv(a, z), D(0));
        var conclusion = All("j", Fin(n), Exists("z", A, And(Zero(Sym("z")), Mem(Sym("z"), Invoke("cstarDisc", App(a, Sym("j")), D(1))))));
        var body = All("n", Nat(), Imp(Le(D(2), n), All("a", Arr(Fin(n), A), Imp(All("j", Fin(n), Mem(App(a, Sym("j")), Invoke("cstarDisc", D(0), D(1)))), All("b", Arr(Fin(Invoke("Nat.sub", n, D(1))), A), Imp(All("k", Fin(Invoke("Nat.sub", n, D(1))), Zero(App(b, Sym("k")))), Imp(All("k", Fin(Invoke("Nat.sub", n, D(1))), Mem(App(b, Sym("k")), Invoke("cstarDisc", D(0), D(1)))), Imp(All("k", Fin(Invoke("Nat.sub", n, D(1))), Invoke("IsConvexForm", a, App(b, Sym("k")))), conclusion))))))));
        if (commutative) body = Imp(Invoke("Dense", Seq(OpenBrace, Sym("x"), Colon, A, Mid, Invoke("IsUnit", Sym("x")), CloseBrace)), body);
        return All("A", Sym("Type"), Instances(A, body, commutative ? "CommCStarAlgebra" : "CStarAlgebra", "PartialOrder", "StarOrderedRing"));
    }
    internal static string SourceClaim(bool commutative) => commutative
        ? "Conjecture 2.4, p. 3: “Let 𝒜 be a unital commutative C*-algebra and G(𝒜) be dense in 𝒜. Let n ∈ ℕ∖{1} and p(z)=(z−a₁)(z−a₂)⋯(z−aₙ)∈𝒜[z] be such that a₁, a₂, …, aₙ ∈ 𝔻̅*(0,1). Assume that p′ admits roots in 𝒜, say b₁, b₂, …, bₙ₋₁ ∈ 𝔻̅*(0,1) and each bₖ can be written in the form of Equation (1). Then for each aⱼ, 1≤j≤n, there exists a zero b of p′ such that b ∈ 𝔻̅*(aⱼ,1).”"
        : "Conjecture 2.5, p. 3: “Let 𝒜 be a unital C*-algebra. Let n ∈ ℕ∖{1} and p(z)=(z−a₁)(z−a₂)⋯(z−aₙ)∈𝒜[z] be such that a₁, a₂, …, aₙ ∈ 𝔻̅*(0,1). Define p′(z)=∑_{j=1}ⁿ (z−a₁)⋯(z−aⱼ)̂⋯(z−aₙ), ∀z∈𝒜, where the term with cap is missing. Assume that p′ admits roots in 𝒜, say b₁, b₂, …, bₙ₋₁ ∈ 𝔻̅*(0,1) and each bₖ can be written in the form of Equation (1). Then for each aⱼ, 1≤j≤n, there exists a zero b of p′ such that b ∈ 𝔻̅*(aⱼ,1).”";
}
