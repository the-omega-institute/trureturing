using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class OmegaQuadraticAndSchurDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur";

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), x = F.Id("x"), y = F.Id("y");
        Formula z = F.Id("z"), w = F.Id("w"), n = F.Id("n"), s = F.Id("s");
        Formula zero = D(0), one = D(1), two = D(2);
        Formula integers = Seq(Mathbb, Grp(F.Id("Z"))), rationals = Seq(Mathbb, Grp(F.Id("Q")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N"))), quadratic = Call("Quad", b, c);
        Formula phi = Varphi, normZ = Call("N", z), normW = Call("N", w);
        Formula shift = Mul(Div(b, c), x);
        Formula minimum = Mul(Sub(a, Div(Sq(b), c)), Sq(x));
        Formula form = Add(Mul(a, Sq(x)), Add(Mul(Mul(Mul(two, b), x), y), Mul(c, Sq(y))));
        Formula minimumPoint = Call("neg", shift);
        Formula minimumForm = Add(Mul(a, Sq(x)), Add(Mul(Mul(Mul(two, b), x), minimumPoint), Mul(c, Sq(minimumPoint))));
        Formula sequence = Call("ListsOfPairs", rationals);
        Formula uv = Call("sumUV", s), uu = Call("sumU", s), vv = Call("sumV", s);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact quadratic algebras and rational positivity for Chapter 32, section 32.8, and Appendix Q.",
            H("Quadratic norms and rational Schur complements"),
            Blocks(
                Law("quadratic-norm-product", "quadratic_norm_mul", "Quadratic norms multiply",
                    Bound(integers, Bound(quadratic, Eq(Call("N", Mul(z, w)), Mul(normZ, normW)), "z", "w"), "b", "c"),
                    "The algebra uses the relation alpha squared equals b times alpha plus c. The norm is the scalar coefficient of the product with the conjugate."),
                Law("quadratic-inverse", "quadratic_mul_inv", "Inversion by nonzero norm",
                    Bound(integers, Bound(quadratic, If(Ne(normZ, zero), Eq(Mul(z, Call("inv", z)), one)), "z"), "b", "c"),
                    "The inverse divides the conjugate by the norm. Cross multiplication compares finite signed fractions, including negative norms."),
                Law("golden-fibonacci", "phi_fibonacci", "Fibonacci coefficients of golden powers",
                    Bound(naturals, Eq(new Formula.Power(phi, Add(n, one)),
                        Add(Call("F", n), Mul(Call("F", Add(n, one)), phi))), "n"),
                    "Multiplying by the golden generator takes coefficients x and y to y and x plus y. The starting coefficients are zero and one."),
                Law("golden-power-norm", "phi_power_norm", "Norm of every golden power",
                    Bound(naturals, Eq(Call("N", new Formula.Power(phi, n)),
                        new Formula.Power(Seq(Open, Minus, one, Close), n)), "n"),
                    "The generator has norm minus one, and the unit has norm one."),
                Law("square-root-two-spinor", "sqrt_two_spinor", "The right-angle spinor closes after eight powers",
                    And(Eq(Call("normSq", F.Id("u")), one), Eq(new Formula.Power(F.Id("u"), D(8)), one)),
                    "Here u denotes the spinor with both coordinates equal to half the square-root-two generator. Its square has scalar coordinate zero and imaginary coordinate one."),
                Law("square-root-two-bell", "sqrt_two_bell", "The squared CHSH value is eight",
                    Eq(Sq(Mul(two, DeltaLower)), D(8)),
                    "The square-root-two generator has square two."),
                Law("rational-lagrange-gram", "rational_lagrange_gram", "Lagrange's Gram identity",
                    Bound(sequence, Eq(Sub(Mul(uu, vv), Sq(uv)), Call("minorSquares", s)), "s"),
                    "The sequence s consists of pairs of rational coordinates. The sums sumU and sumV are the sums of coordinate squares, and sumUV is their dot product. The right side adds the squared alternating minors over all pairs of positions with the first position smaller than the second."),
                Law("rational-cauchy-schwarz", "rational_cauchy_schwarz", "Rational Cauchy–Schwarz",
                    Bound(sequence, Le(Sq(uv), Mul(uu, vv)), "s"),
                    "Each summand in the Gram identity is a rational square and therefore nonnegative."),
                Law("rational-schur-complete", "rational_schur_complete", "Schur completion of the square",
                    Bound(rationals, If(Ne(c, zero), Eq(form, Add(minimum, Mul(c, Sq(Add(y, shift)))))), "a", "b", "c", "x", "y"),
                    "The pivot c is a finite nonzero rational. The correction to the first diagonal coefficient is b squared divided by c."),
                Law("rational-schur-minimum", "rational_schur_min", "The Schur residual is an attained minimum",
                    Bound(rationals, If(Lt(zero, c),
                        And(Bound(rationals, Le(minimum, form), "y"), Eq(minimumForm, minimum))), "a", "b", "c", "x"),
                    "With a positive pivot the completed square is nonnegative. It vanishes at y equal to the negative of the shift."))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Bound(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Sq(Formula term) => new Formula.Power(term, D(2));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula If(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static DocumentBlock.Describe Law(string id, string selector, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{selector}"),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
