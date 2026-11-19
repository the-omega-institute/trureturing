using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class PrimitivePayoffSwitchingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PrimitivePayoffSwitching.";
    private static readonly Formula R = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula N = Seq(Mathbb, Grp(F.Id("N")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reweighted switching costs bound mechanical endpoint minima and force bounded discrepancy.",
        H("Finite Endpoint Costs for Switching Payoffs"),
        Blocks(
            Paragraph(DefinitionDsl.Text(
                "A binary H window of length n is paired with a G response p of n + 1 Boolean vertices. "
                + "The cost adds the signed discrepancy contribution of each source vertex and charges "
                + "two for a switch. The sign σ takes values −1 and +1. The mechanical word M has slope "
                + "α and intercept ρ. Its centered fractional part Q is evaluated at the path boundaries.")),
            Describe.Lean(
                DescribeId.Create("reweighted-path-lower-bound"),
                DeclarationHandle.Create(Owner + "mechanical_cost_ge_boundary"),
                H("Lower bound for every reweighted path"),
                StatementSource.FromAuthor(Disp(PathBound())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "Transferring the signed potential across each edge gives a telescoping correction. "
                    + "Each reweighted term is zero on a constant edge and at least one on a switch. "
                    + "The path cost is therefore bounded below by the initial signed potential minus the final one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-endpoint-minima"),
                DeclarationHandle.Create(Owner + "mechanical_endpointMinimum_diagonal"),
                H("Constant paths attain the diagonal minima"),
                StatementSource.FromAuthor(Disp(Diagonal())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "For a response returning to vertex s, the constant path attains the potential bound. "
                    + "The diagonal minimum is σ(s) times the mechanical discrepancy. The two diagonal "
                    + "minima are negatives of each other. The endpoint-pair comparison rules out a strict increase in both."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonimprovable-discrepancy"),
                DeclarationHandle.Create(Owner + "nonimprovable_abs_discrepancy_le_seven"),
                H("Discrepancy bound for nonimprovable windows"),
                StatementSource.FromAuthor(Disp(DiscrepancyBound())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "The mechanical endpoint minima are all at least −1. A window with absolute "
                    + "discrepancy above seven admits a favorable interior sign. Patching the prescribed "
                    + "endpoints adds at most six to the constant-sign cost, so all its endpoint minima are "
                    + "below −1. A single mechanical window strictly improves every entry."))),
                DescribeRole.Theorem))));

    private static Formula PathBound()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var p = F.Id("p");
        var m = Apply("M", Alpha, Rho, i, n);
        var left = Multiply(Apply("sign", Apply("p", D(0))), Apply("Q", Alpha, Rho, i));
        var right = Multiply(Apply("sign", Apply("p", n)), Apply("Q", Alpha, Rho, Add(i, n)));
        var response = new Formula.TypeArrow(Apply("Fin", Add(n, D(1))), F.Id("Bool"));
        return MechanicalParameters(All(n, N, All(i, N, All(p, response,
            AtMost(Subtract(left, right), Apply("cost", Alpha, m, p))))));
    }

    private static Formula Diagonal()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var s = F.Id("s");
        var m = Apply("M", Alpha, Rho, i, n);
        return MechanicalParameters(All(n, N, ImpliesOf(Less(D(0), n),
            All(i, N, All(s, F.Id("Bool"), Equal(Apply("endpointMinimum", Alpha, m, s, s),
                Multiply(Apply("sign", s), Apply("discrepancy", Alpha, m))))))));
    }

    private static Formula DiscrepancyBound()
    {
        var n = F.Id("n");
        var w = F.Id("w");
        var word = new Formula.TypeArrow(Apply("Fin", n), F.Id("Bool"));
        return All(Alpha, R, ImpliesOf(SlopeBounds(), All(n, N, ImpliesOf(AtMost(D(2), n),
            All(w, word, ImpliesOf(Apply("Nonimprovable", Alpha, w),
                AtMost(new Formula.Absolute(Apply("discrepancy", Alpha, w)), D(7))))))));
    }

    private static Formula MechanicalParameters(Formula body) =>
        All(Alpha, R, All(Rho, R, ImpliesOf(SlopeBounds(), body)));
    private static Formula SlopeBounds() =>
        new Formula.Logic(AtMost(D(0), Alpha), FormulaLogicOperator.And, Less(Alpha, D(1)));
    private static Formula Apply(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, Open, variable, Colon, Sp, domain, Close, Comma, Sp, body);
    private static Formula ImpliesOf(Formula premise, Formula conclusion) =>
        new Formula.Logic(Seq(Open, premise, Close), FormulaLogicOperator.Implies,
            Seq(Open, conclusion, Close));
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
