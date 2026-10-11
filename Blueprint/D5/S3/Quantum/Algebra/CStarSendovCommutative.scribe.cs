using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.CStarSendovCommutativeFormulas;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CStarSendovCommutativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CStarSendovCommutative.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dense invertibles and the literal C*-derivative give the commutative Sendov refutation.",
        H("CStarSendovCommutative"), Blocks(
            Node("HasCStarDeriv", "The C*-algebraic derivative", DerivativeFormula(),
                "Definition 2.1 (C*-algebraic differentiation), p. 2: “Let 𝒜 be a unital commutative C*-algebra and G(𝒜) be dense in 𝒜. Let f: 𝒜→𝒜 be a function and ω∈𝒜. We say that f is C*-algebraic differentiable at ω if there exists an L∈𝒜 satisfying the following: for each ε>0, there exists a δ>0 such that if z∈𝒜 satisfies ‖z−ω‖<δ and z−ω∈G(𝒜), then ‖(z−ω)⁻¹(f(z)−f(ω))−L‖<ε. In this case, we write f′(ω)=L.” The predicate states the displayed condition for a specified L. Dense invertibles are required by the claim. Ring.inverse agrees with the unit inverse on the tested increments.", DescribeRole.Definition, true),
            Node("claimSendovCommutative", "Krishna's Conjecture 2.4", Iff(Sym("claimSendovCommutative"), Claim(true)),
                SourceClaim(true) + " The encoding uses zero-based Fin indices, degrees 2≤n, and unital commutative C*-algebras in Type with PartialOrder and StarOrderedRing. A zero at z is HasCStarDeriv (orderedPoly a) z 0. For every root the conclusion asks for an algebra-valued derivative zero in its unit disc.", DescribeRole.Definition, true),
            Node("result", "Conjecture 2.4 is false", new Formula.Not(Sym("claimSendovCommutative")),
                "Invertibles are dense in C(Set.Icc 0 6,ℂ): polynomial approximation gives a smooth approximant, and its image has dense complement by the real dimension inequality. A small translation avoids zero. For the cubic, the exact invertible-increment identity identifies Definition 2.1 with orderedDeriv. The two critical branches then give the same obstruction to the disc around 1/2.", DescribeRole.Theorem, false))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature = false, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula DerivativeFormula()
    {
        var A = Sym("A"); var f = Sym("f"); var w = Sym("w"); var L = Sym("L"); var z = Sym("z");
        var condition = All("e", Real(), Imp(Lt(D(0), Sym("e")), Exists("d", Real(), And(Lt(D(0), Sym("d")), All("z", A, Imp(Lt(Norm(Sub(z, w)), Sym("d")), Imp(Invoke("IsUnit", Sub(z, w)), Lt(Norm(Sub(Mul(Invoke("Ring.inverse", Sub(z, w)), Sub(App(f, z), App(f, w))), L)), Sym("e")))))))));
        return All("A", Sym("Type"), Instances(A, All("f", Arr(A, A), All("w", A, All("L", A, Iff(Invoke("HasCStarDeriv", f, w, L), condition)))), "NormedRing"));
    }
}

internal static class CStarSendovCommutativeFormulas
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
    internal static Formula SquareRootRealPart(Formula z) => Invoke("Complex.re", Invoke("Complex.cpow", z, Invoke("Inv.inv", Cast(D(2), Complex()))));
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
    private static Formula Clamp(Formula t) => Invoke("min", D(1), Invoke("max", D(0), t));
    internal static Formula Cx() => Sub(Sub(Plus(Plus(Negate(Rat(9, 10, Real())), Mul(Rat(4, 5, Real()), Clamp(Sym("t")))), Mul(Rat(1, 5, Real()), Clamp(Sub(Sym("t"), D(1))))), Mul(Rat(1, 5, Real()), Clamp(Sub(Sym("t"), D(3))))), Mul(Rat(4, 5, Real()), Clamp(Sub(Sym("t"), D(5)))));
    internal static Formula Cy() => Sub(Sub(Plus(Mul(Rat(4, 5, Real()), Clamp(Sym("t"))), Mul(Rat(1, 10, Real()), Clamp(Sub(Sym("t"), D(2))))), Mul(Rat(1, 10, Real()), Clamp(Sub(Sym("t"), D(4))))), Mul(Rat(4, 5, Real()), Clamp(Sub(Sym("t"), D(5)))));
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
    internal static Formula PolynomialFormula()
    {
        var A = Sym("A"); var n = Sym("n"); var a = Sym("a"); var z = Sym("z");
        var list = Invoke("List.ofFn", Seq(Parenthesized(Typed(Sym("i"), Fin(n))), Sp, Mapsto, Sp, Sub(z, App(a, Sym("i")))));
        return All("A", Sym("Type"), Instances(A, All("n", Nat(), All("a", Arr(Fin(n), A), All("z", A, Eq(Invoke("CStarDualMeanValue.orderedPoly", a, z), Invoke("List.prod", list))))), "Ring"));
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
