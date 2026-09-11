using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class PolynomialExponentSelfDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/PolynomialExponentSelfDivisibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial exponents divide their vanishing-diagonal coefficients.",
        H("Polynomial Exponent Divisibility for Vanishing Diagonals"),
        Blocks(
            Node("polynomial_exponent_self_divisibility", "Polynomial exponent theorem",
                GeneralFormula(), "Positive integer polynomial exponents normalized at one divide their coefficients.", AssessedProvenance.FromRepo()),
            Node("affine_polynomial_exponent_self_divisibility", "Affine polynomial instance",
                AffineFormula(), "The affine polynomial instance recovers the frozen affine theorem, including slope zero.", AssessedProvenance.FromRepo()),
            Node("monomial_exponent_self_divisibility", "Monomial polynomial instance",
                MonomialFormula(), "The monomial instance follows from the polynomial theorem.", AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("polynomial-exponent-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula I(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(n))), [.. a]);
    private static Formula Eval(Formula p, Formula n) => Call("eval", p, n);
    private static Formula Pos(Formula x) => Seq(D(1), Sp, Le, Sp, x);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Sp, Implies, Sp, Parenthesized(q));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Div(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula Conj(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula GeneralFormula() => Disp(Seq(PolyBound(),
        Imp(Conj(Seq(Eval(I("P"), D(1)), Sp, Eq, Sp, D(1)),
            Seq(Forall, Sp, I("n"), Colon, Sp, Naturals(), Comma, Sp,
                Imp(Pos(I("n")), Seq(D(1), Sp, Le, Sp, Eval(I("P"), I("n")))))),
            Seq(Forall, Sp, I("n"), Colon, Sp, Naturals(), Comma, Sp,
                Imp(Pos(I("n")), Div(Eval(I("P"), I("n")),
                    Call("a", Call("fun", I("m"), Call("toNat", Eval(I("P"), I("m")))), I("n"))))))));
    private static Formula PolyBound() => Seq(Forall, Sp, I("P"), Colon, Sp, F.Id("Polynomial"), Sp, Seq(Mathbb, Grp(F.Id("Z"))), Comma, Sp);
    private static Formula Bound(string name) => Seq(Forall, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp);
    private static Formula AffineFormula() => Disp(Seq(Bound("d"), Sp, Bound("n"), Imp(Pos(I("n")),
        Div(Eval(Seq(Call("C", I("d")), Sp, Star, Sp, Parenthesized(Seq(F.Id("X"), Sp, Minus, Sp, D(1))), Sp, Plus, Sp, D(1)), I("n")),
            Call("a", Seq(I("d"), Sp, Plus, Sp, D(1)), I("n"))))));
    private static Formula MonomialFormula() => Disp(Seq(Bound("k"), Sp, Bound("n"), Imp(Pos(I("n")),
        Div(Seq(Parenthesized(I("n")), Sp, Caret, Sp, I("k")), Call("a", Call("fun", I("m"), Seq(I("m"), Sp, Caret, Sp, I("k"))), I("n"))))));
}
