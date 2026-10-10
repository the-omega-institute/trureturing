using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CStarSmaleHigherOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CStarSmaleHigherOrder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/krishna2022cstarsmale");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The higher-order C*-algebraic Smale mean value conjecture fails at degree three in Complex x Complex with its supremum norm.",
        H("A degree-three counterexample to the higher-order C*-algebraic Smale conjecture"),
        Blocks(
            Node("smale-polynomial", "The factor polynomial", "smalePoly", PolynomialFormula(),
                @"Section 2, Conjecture HIGHERMEAN (journal p. 44, Conjecture 2.3): ""Let P(z) ≔ (z−a₁)⋯(z−aₙ) be a polynomial of degree n ≥ 2 over 𝒜, a₁, …, aₙ ∈ 𝒜."" The polynomial is a product in Polynomial A; its value at z is Polynomial.eval z (smalePoly a). The index j : Fin n denotes the source's a_(j+1), retaining all n factors with multiplicity. The definition applies to every commutative ring; the conjecture specializes it to a commutative C*-algebra.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture HIGHERMEAN", "claim", ClaimFormula(),
                @"Section 2, Conjecture HIGHERMEAN (journal p. 44, Conjecture 2.3), verbatim: ""Let 𝒜 be a commutative C*-algebra. Let P(z) ≔ (z−a₁)⋯(z−aₙ) be a polynomial of degree n ≥ 2 over 𝒜, a₁, …, aₙ ∈ 𝒜. If z ∈ 𝒜 is not a critical point of P, then there exists a critical point w ∈ 𝒜 of P such that ‖P⁽ᵏ⁾(z)‖/k! · ‖P(z)−P(w)‖ᵏ⁻¹/‖P′(z)‖ᵏ ≤ 4ᵏ⁻¹, ∀ 2 ≤ k ≤ n."" CommCStarAlgebra encodes a unital complex commutative C*-algebra. The sum of products with one factor omitted is Polynomial.derivative_prod, and P^(k) is Function.iterate Polynomial.derivative k applied to smalePoly a. Noncritical means the first derivative is nonzero. One w must satisfy every k inequality. Natural subtraction k−1 is truncated subtraction, agreeing with ordinary subtraction for k≥2; factorial is coerced from Nat to Real and every norm and quotient is real-valued. The displayed fractions are division in Real.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The higher-order conjecture is false", "result",
                Disp(Seq(Neg, Sp, F.Id("claim"))),
                "Take A = Complex x Complex, n = 3 and z = 0. The roots are (0,0), ((−21+sqrt(437))/2,sqrt(3)) and ((−21−sqrt(437))/2,−sqrt(3)), with real entries embedded into Complex. Their factor product evaluates to (x^3+21x^2+x,y^3−3y). The complete critical set consists of (−7+sqrt(438)/3,1), (−7+sqrt(438)/3,−1), (−7−sqrt(438)/3,1) and (−7−sqrt(438)/3,−1). Its second coordinate forces the norm of P(0)−P(w) to be at least 2. The first and second derivative norms at zero are 3 and 42. Thus the k = 2 expression is at least (42/2)(2/9) = 14/3 > 4 for every critical point. The supremum norm takes the curvature from the first coordinate and the unavoidable critical-value gap from the second; applying the scalar theorem separately does not bound this product of maxima. The source's degree-2 theorem and its scalar higher-order theorem retain their stated scopes.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("krishna-2022-cstar-higher-order-smale-mean-value"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Norm(Formula value) => Seq(Vert, value, Vert);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula Poly() => Call("smalePoly", V("a"));
    private static Formula Eval(Formula polynomial, Formula point) =>
        App(Qualified("Polynomial", "eval"), point, polynomial);
    private static Formula Deriv() => App(Qualified("Polynomial", "derivative"), Poly());
    private static Formula IteratedDerivative() =>
        App(Qualified("Function", "iterate"), Qualified("Polynomial", "derivative"), V("k"), Poly());

    private static Formula PolynomialFormula()
    {
        Formula a = V("a"), j = V("j"), n = V("n"), type = V("A");
        Formula factor = Subtract(Qualified("Polynomial", "X"),
            App(Qualified("Polynomial", "C"), App(a, j)));
        Formula product = Seq(new Formula.Subscript(Prod,
            Seq(j, Colon, Sp, Call("Fin", n))), Parenthesized(factor));
        return Disp(All("A", V("Type"), Inst(Call("CommRing", type), All("n", Nat(),
            All("a", new Formula.TypeArrow(Call("Fin", n), type), Equal(Poly(), product))))));
    }

    private static Formula ClaimFormula()
    {
        Formula type = V("A"), n = V("n"), k = V("k"), z = V("z"), w = V("w");
        Formula exponent = Subtract(k, D(1));
        Formula factorial = Seq(Parenthesized(Seq(App(Qualified("Nat", "factorial"), k),
            Colon, Sp, Real())));
        Formula gap = Norm(Subtract(Eval(Poly(), z), Eval(Poly(), w)));
        Formula ratio = Multiply(
            new Formula.Fraction(Norm(Eval(IteratedDerivative(), z)), factorial),
            new Formula.Fraction(Pow(gap, exponent), Pow(Norm(Eval(Deriv(), z)), k)));
        Formula bound = new Formula.Relation(ratio, FormulaRelationOperator.LessThanOrEqual,
            Pow(D(4), exponent));
        Formula allK = All("k", Nat(), Implies(new Formula.Relation(D(2),
            FormulaRelationOperator.LessThanOrEqual, k), Implies(new Formula.Relation(k,
            FormulaRelationOperator.LessThanOrEqual, n), bound)));
        Formula critical = Some("w", type, And(Equal(Eval(Deriv(), w), D(0)), allK));
        Formula quantified = All("A", V("Type"), Inst(Call("CommCStarAlgebra", type),
            All("n", Nat(), Implies(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n),
                All("a", new Formula.TypeArrow(Call("Fin", n), type), All("z", type,
                    Implies(NotEqual(Eval(Deriv(), z), D(0)), critical)))))));
        return Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, Parenthesized(quantified)));
    }
}
