using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCriticalQuarticDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCriticalQuartic.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");
    private static readonly Formula Real = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula Vector = new Formula.Power(Real, D(2));
    private static readonly Formula Nonzero = new Formula.Relation(F.Id("v"), FormulaRelationOperator.NotEqual, D(0));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict exponent decrease of the positive-temperature Wu quartic kernel.",
        H("The normalized Gibbs quartic at positive inverse temperature"),
        Blocks(
            Paragraph(Text("Wu v1, §3.2, Corollary 3.2 and (3.19), supplies the one-qubit Gibbs dynamics. In the scalar reduction, divide the weighted fourth-order coefficients by the square of the second-order coherence coefficient and translate the population coordinate by writing its original value as s + 1. The resulting coefficients and their strict comparison are derived here. Lean checks the reduced scalar formulas at β > 0 and real exponents above one. The signed-model Taylor identification and Wu’s Conjecture 3.14 lie outside these statements.")),
            Paragraph(Text("Fix real inverse temperature β > 0. For q > 1 set x = β/(2q), y = β/2 − x, R = coth x and S = coth y. Write U = 1/sinh² x, V = 1/sinh² y and A = (y/x)(V/U). The reduced population and coherence coefficients are a = A/2, e = S − A(R − 1), and d = −1 + (1 − R/2)S + A(R − 1)²/2. The symmetric matrix K has diagonal a, d and both off-diagonal entries e/2. Write value(β,q,v) for vᵀ K v. The function valueAlongExponent(β,v) sends t to value(β,t,v).")),
            Paragraph(Text("In the exponential coordinates set z = exp(−β), k = z^(1/q), u = z/k, g = 1 − u and h = 1 − k. Then exponentA = (q − 1)(z/k²)h²/(2g²), exponentE = 2/g − 1 − 2(q − 1)uh/g², and exponentD = 2/g − 3/2 − (1 + z)/(gh) + 2(q − 1)z/g². Write ΔA = exponentA(β,p) − exponentA(β,r), with ΔE and ΔD defined by the respective endpoint differences.")),
            Entry("derivative", "deriv_value_neg", "Pointwise strict decrease",
                new Formula.BindMany(FormulaQuantifier.ForAll,
                    [Variable("beta", Real), Variable("q", Real), Variable("v", Vector)],
                    Under(And(Lt(D(0), F.Id("beta")), And(Lt(D(1), F.Id("q")), Nonzero)),
                        Lt(Call("deriv", Call("valueAlongExponent", F.Id("beta"), F.Id("v")), F.Id("q")), D(0)))),
                "Set Λ = 2(R + S) − 1/x − 1/y. For s = v₀ − (R − 1)v₁ and t = v₁, the derivative is −x/(2q) times the quadratic form in (s,t) with leading entry AΛ, mixed matrix entry V + UA, and trailing entry US + RV. The determinant is V²/x² times the product of 2xy(R + S) − (x + y) and sinh x cosh x + sinh y cosh y, minus (x + y)² inside the same factor. The reciprocal bound for coth gives Λ ≥ 1/x + 1/y > 0 and bounds the first product factor below by x + y. The second product factor strictly exceeds x + y, so the determinant is positive. Completion of the square gives strict positivity of the form for nonzero (s,t)."),
            Entry("endpoint", "endpoint_drop_pos", "Strict Loewner drop",
                AtEndpoints(Lt(D(0), Sub(Call("value", F.Id("beta"), F.Id("p"), F.Id("v")),
                    Call("value", F.Id("beta"), F.Id("r"), F.Id("v")))), withVector: true),
                "The mean value theorem applies to the quadratic form with the vector held fixed throughout the exponent interval."),
            Entry("schur", "endpoint_schur_pos", "Strict Schur complement",
                AtEndpoints(And(Lt(D(0), Difference("a")),
                    Lt(D(0), Schur(Difference("a"), Difference("e"), Difference("d"))))),
                "Write Δa, Δe and Δd for the hyperbolic endpoint differences. Evaluate the positive endpoint form at (1,0) and at (−Δe/(2Δa),1)."),
            Entry("exponential-schur", "exponent_endpoint_schur_pos", "Positive attained minimum for the Gibbs coefficients",
                ExponentialSchur(),
                "Use k = exp(−2x), u = exp(−2y), z = ku and q − 1 = y/x to identify the coefficients at both endpoints. Completing the square in the exponential endpoint polynomial gives the lower bound and shows that it is attained at s = −ΔE/(2ΔA)."))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula ExponentialSchur()
    {
        var a = Seq(Delta, Sp, F.Id("A"));
        var e = Seq(Delta, Sp, F.Id("E"));
        var d = Seq(Delta, Sp, F.Id("D"));
        var s = F.Id("s");
        var complement = Schur(a, e, d);
        var polynomial = new Formula.Binary(
            new Formula.Binary(Mul(a, new Formula.Power(s, D(2))), FormulaBinaryOperator.Add, Mul(e, s)),
            FormulaBinaryOperator.Add, d);
        var minimum = Seq(new Formula.Subscript(Min, Seq(s, Sp, InMacro, Sp, Real)),
            Sp, Open, polynomial, Close);
        return AtEndpoints(And(Lt(D(0), a), And(Lt(D(0), complement),
            new Formula.Relation(complement, FormulaRelationOperator.Equal, minimum))));
    }

    private static Formula AtEndpoints(Formula claim, bool withVector = false)
    {
        var beta = Variable("beta", Real);
        var p = Variable("p", Real);
        var r = Variable("r", Real);
        var ordered = And(Lt(D(0), F.Id("beta")), And(Lt(D(1), F.Id("p")), Lt(F.Id("p"), F.Id("r"))));
        return withVector
            ? new Formula.BindMany(FormulaQuantifier.ForAll, [beta, p, r, Variable("v", Vector)],
                Under(And(ordered, Nonzero), claim))
            : new Formula.BindMany(FormulaQuantifier.ForAll, [beta, p, r], Under(ordered, claim));
    }

    private static Formula.BoundVariable Variable(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Under(Formula premises, Formula claim) =>
        new Formula.Logic(premises, FormulaLogicOperator.Implies, claim);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Schur(Formula a, Formula e, Formula d) =>
        Sub(d, new Formula.Fraction(new Formula.Power(e, D(2)), Mul(D(4), a)));

    private static Formula Difference(string name) =>
        Sub(Call(name, F.Id("beta"), F.Id("p")), Call(name, F.Id("beta"), F.Id("r")));
}
