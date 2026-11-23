using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCriticalQuarticDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCriticalQuartic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict exponent decrease of the positive-temperature Wu quartic kernel.",
        H("The normalized Gibbs quartic at positive inverse temperature"),
        Blocks(
            Paragraph(Text("Fix real inverse temperature β > 0. For q > 1 set x = β/(2q), y = β/2 − x, R = coth x and S = coth y. Write U = 1/sinh² x, V = 1/sinh² y and A = (y/x)(V/U). The reduced population and coherence coefficients are a = A/2, e = S − A(R − 1), and d = −1 + (1 − R/2)S + A(R − 1)²/2. The symmetric matrix K has diagonal a, d and both off-diagonal entries e/2. Write value(β,q,v) for vᵀ K v.")),
            Entry("derivative", "deriv_value_neg", "Pointwise strict decrease",
                Lt(Call("deriv", Call("valueAlongExponent", F.Id("beta"), F.Id("v")), F.Id("q")), D(0)),
                "For every real β > 0, q > 1 and every nonzero v in ℝ², the displayed derivative is negative. The function valueAlongExponent(β,v) sends t to value(β,t,v).",
                "Set Λ = 2(R + S) − 1/x − 1/y. For s = v₀ − (R − 1)v₁ and t = v₁, the derivative is −x/(2q) times the quadratic form in (s,t) with leading entry AΛ, mixed matrix entry V + UA, and trailing entry US + RV. The determinant is V²/x² times the product of 2xy(R + S) − (x + y) and sinh x cosh x + sinh y cosh y, minus (x + y)² inside the same factor. Each product factor strictly exceeds x + y. The leading entry is positive and completion of the square proves strict positivity of the form for nonzero (s,t)."),
            Entry("endpoint", "endpoint_drop_pos", "Strict Loewner drop",
                Lt(D(0), Sub(Call("value", F.Id("beta"), F.Id("p"), F.Id("v")),
                    Call("value", F.Id("beta"), F.Id("r"), F.Id("v")))),
                "For every real β > 0, 1 < p < r and every nonzero v in ℝ², the displayed difference is positive.",
                "The mean value theorem applies to the quadratic form with the vector held fixed throughout the exponent interval."),
            Entry("schur", "endpoint_schur_pos", "Strict Schur complement",
                new Formula.Logic(Lt(D(0), Delta("a")), FormulaLogicOperator.And,
                    Lt(D(0), Sub(Delta("d"), new Formula.Fraction(new Formula.Power(Delta("e"), D(2)),
                        new Formula.Binary(D(4), FormulaBinaryOperator.Multiply, Delta("a")))))),
                "For every real β > 0 and 1 < p < r, write Δa = a(β,p) − a(β,r) and define Δe and Δd by the same endpoint difference. Both displayed inequalities hold.",
                "Evaluate the positive endpoint form at (1,0) and at (−Δe/(2Δa),1)."))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula Delta(string name) =>
        Sub(Call(name, F.Id("beta"), F.Id("p")), Call(name, F.Id("beta"), F.Id("r")));
}
