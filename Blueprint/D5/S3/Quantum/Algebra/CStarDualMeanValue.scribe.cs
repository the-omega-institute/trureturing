using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CStarDualMeanValueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CStarDualMeanValue.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/krishna2022cstarsmale");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cubic in the product of two complex fields refutes the dual mean value bound.",
        H("CStarDualMeanValue"), Blocks(
            Node("orderedPoly", "The ordered polynomial", PolynomialFormula(),
                "Section 2, p. 4: “Let 𝒜 be a C*-algebra. For P(z) ≔ (z−a₁)(z−a₂)⋯(z−aₙ) for all z∈𝒜 with a₁, a₂, …, aₙ ∈ 𝒜, we define P′(z)=∑ⱼ₌₁ⁿ (z−a₁)⋯(z−aⱼ)̂⋯(z−aₙ), ∀z∈𝒜 where the term with cap is missing.” The polynomial preserves the factor order through List.ofFn and List.prod. The indices are zero-based Fin d. The ordered derivative is CStarSchoenberg.orderedDeriv, with the omitted factor removed by List.eraseIdx.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The C*-algebraic dual mean value conjecture", ClaimFormula(),
                "Conjecture DUALSMALE (Conjecture 3.1), Section 3, p. 7: “Let 𝒜 be a commutative C*-algebra. Let P(z) ≔ (z−a₁)⋯(z−aₙ) be a polynomial of degree n ≥ 2 over 𝒜, a₁, …, aₙ ∈ 𝒜. If z∈𝒜 is not a critical point of P, then there exists a critical point w∈𝒜 of P such that ‖P′(z)‖/deg(P) = ‖P′(z)‖/n ≤ ‖P(z)−P(w)‖/‖z−w‖.” The roots a use zero-based Fin n indices. Noncritical means CStarSchoenberg.orderedDeriv a z ≠ 0, as in the source's gloss in Section 2; critical means CStarSchoenberg.orderedDeriv a w = 0. The degree n is cast to ℝ. CommCStarAlgebra restricts A to unital commutative C*-algebras in Type, weakening the universal assertion, so a counterexample in this subclass refutes the source statement.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The norm-form conjecture is false", new Formula.Not(Named("claim")),
                "Take A = ℂ × ℂ, n = 3, z = (0,0) and roots (0,3/2), (3,3/2), (3,3/2). The polynomial is (x(x−3)²,(y−3/2)³), and its ordered derivative is (3(x−1)(x−3),3(y−3/2)²). The only critical points are (1,3/2) and (3,3/2). At z = 0 the derivative is (9,27/4), whose supremum norm is 9. The two difference quotients are 8/3 and 9/8, both strictly below the required threshold 3. At the first critical point the second coordinate enlarges the denominator from 1 to 3/2 while the numerator norm remains 4; at the second the first coordinate contributes zero to the polynomial difference. Thus the scalar lower bound fails to pass to the supremum norm on products. The source's degree-two theorem remains intact.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Deriv(Formula a, Formula z) => new Formula.Apply(
        Qualified("CStarSchoenberg", "orderedDeriv"), [a, z]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string v, Formula type, Formula body) => Seq(
        Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string v, Formula type, Formula body) => Seq(
        Exists, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(
        Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(
        Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Bracket(Formula value) => Seq(OpenBracket, value, CloseBracket, Sp);

    private static Formula PolynomialFormula()
    {
        Formula A = F.Id("A"), d = F.Id("d"), a = F.Id("a"), z = F.Id("z"), i = F.Id("i");
        Formula mapping = Seq(Parenthesized(Seq(i, Colon, Fin(d))), Sp, Mapsto, Sp,
            Sub(z, new Formula.Apply(a, [i])));
        Formula list = new Formula.Apply(Qualified("List", "ofFn"), [Parenthesized(mapping)]);
        Formula product = new Formula.Apply(Qualified("List", "prod"), [Parenthesized(list)]);
        return All("A", F.Id("Type"), Seq(Bracket(Call("Ring", A)),
            All("d", Nat(), All("a", new Formula.TypeArrow(Fin(d), A),
                All("z", A, EqTo(Call("orderedPoly", a, z), product))))));
    }

    private static Formula ClaimFormula()
    {
        Formula A = F.Id("A"), n = F.Id("n"), a = F.Id("a"), z = F.Id("z"), w = F.Id("w");
        Formula noncritical = new Formula.Relation(Deriv(a, z), FormulaRelationOperator.NotEqual, D(0));
        Formula threshold = new Formula.Fraction(new Formula.Norm(Deriv(a, z)),
            Parenthesized(Seq(n, Colon, Real())));
        Formula quotient = new Formula.Fraction(
            new Formula.Norm(Sub(Call("orderedPoly", a, z), Call("orderedPoly", a, w))),
            new Formula.Norm(Sub(z, w)));
        Formula body = All("A", F.Id("Type"), Seq(Bracket(Call("CommCStarAlgebra", A)),
            All("n", Nat(), Imp(Le(D(2), n), All("a", new Formula.TypeArrow(Fin(n), A),
                All("z", A, Imp(noncritical,
                    Ex("w", A, And(EqTo(Deriv(a, w), D(0)), Le(threshold, quotient))))))))));
        return EqTo(Named("claim"), Parenthesized(body));
    }
}
