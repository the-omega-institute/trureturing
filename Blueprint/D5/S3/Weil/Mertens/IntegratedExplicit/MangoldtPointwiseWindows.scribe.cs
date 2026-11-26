using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class MangoldtPointwiseWindowsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise windows for the complete Mangoldt remainder",
        H("One-sided bounds on a whole interval"),
        Blocks(
            Paragraph(Text("Write U(x) for x times the sum of Λ(n)/n over 1 ≤ n ≤ x, "
                + "minus ψ(x) and x log x, plus (1+γ)x. Here Λ is the von Mangoldt function, "
                + "ψ its summatory function and γ Euler’s constant. Fix b > 1. A window begins "
                + "at Y ≥ 2 and contains every real x between Y and Yᵇ, including both endpoints.")),
            Describe.Lean(DescribeId.Create("power-windows"),
                DeclarationHandle.Create(Module + "rh_iff_pointwise_power_windows"),
                H("Arbitrarily small positive power losses"),
                StatementSource.FromAuthor(PowerCriterion()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under RH the normalized primitive U(x)/√x is eventually "
                    + "bounded in absolute value. For each k > 0, xᵏ eventually absorbs the "
                    + "fixed coefficient. "
                    + "The starting point may depend on k and the prescribed lower bound R.")),
                    Paragraph(Text("For the converse let q be the integral of (θ(t)−t)/t² "
                    + "from x to infinity and Q the corresponding integral with ψ. The exact "
                    + "identity U(x)/x = −Q(x) and the limit √x(Q(x)−q(x)) → 2 bound the "
                    + "integral of max(−q(x),0)/√x on [Y,Yᵇ] by "
                    + "4 Yᵇᵏ (b−1) log Y. Given any η > 0, choose k = η/(2b). "
                    + "The remaining factor 4(b−1) log Y is at most Y to the power η/2 at all "
                    + "sufficiently large Y. The prime-only window criterion now gives RH."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("square-root-windows"),
                DeclarationHandle.Create(Module + "rh_iff_pointwise_sqrt_windows"),
                H("A fixed coefficient at the square-root scale"),
                StatementSource.FromAuthor(SqrtCriterion()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first Li mass equals 2+γ−2 log(2√π). Under RH the "
                    + "full-axis envelope eventually bounds |U(x)|/√x by any larger C. Conversely, "
                    + "on a sufficiently late window C ≤ xᵏ for every x in that "
                    + "window, for each fixed k > 0. The first criterion gives RH. The proved "
                    + "inequality firstLiMass < 1/3 allows the explicit choice C = 1/3."))),
                DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Real, body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Real, body);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula IffRh(Formula right) => new Formula.Logic(F.Id("RiemannHypothesis"), FormulaLogicOperator.Iff, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Pow(Formula x, Formula exponent) => F.Seq(x, F.Caret, F.Grp(exponent));
    private static Formula At(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula LateWindow(Formula upper)
    {
        var x = F.Id("x");
        var y = F.Id("Y");
        var inside = And(Le(y, x), Le(x, Pow(y, F.Id("b"))));
        var bounds = All("x", Implies(inside, Le(At("U", x), upper)));
        return All("R", Exists("Y", And(Le(At("max", F.Id("R"), F.D(2)), y), bounds)));
    }

    private static Formula PowerCriterion()
    {
        var k = F.Id("k");
        var half = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2)));
        var windows = LateWindow(Pow(F.Id("x"), F.Seq(half, F.Plus, k)));
        return F.Disp(All("b", Implies(Less(F.D(1), F.Id("b")),
            IffRh(All("k", Implies(Less(F.D(0), k), windows))))));
    }

    private static Formula SqrtCriterion()
    {
        var c = F.Id("C");
        var bound = F.Seq(c, F.Sqrt, F.Grp(F.Id("x")));
        return F.Disp(All("C", All("b", Implies(Less(F.Id("firstLiMass"), c),
            Implies(Less(F.D(1), F.Id("b")), IffRh(LateWindow(bound)))))));
    }
}
