using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class CriticalGammaWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concentration of normalized Laplace moments outside a critical window",
        H("Concentration at a fixed multiplicative width"),
        Blocks(Describe.Lean(
            DescribeId.Create("gamma-window"),
            DeclarationHandle.Create("D5/S3/Analytic/Laplace/CriticalGammaWindow.critical_window_off_mass"),
            H("An explicit moment order controls both tails"),
            StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For a real cutoff a ≥ 1 set k = floor(640a). Let S be the part of the "
                    + "positive half-line outside the closed interval [a,3a/2], and write "
                    + "f(u) = |g(u)| uᵏ exp(−512u)/k!. The same k works for every real measurable "
                    + "function g bounded in absolute value by M exp(2u) for u ≥ 0.")),
                Paragraph(Text("After the growth bound, the remaining damping rate is 510. On the "
                    + "left tail use rate 542 with multiplier exp(32a). On the right use rate 478 "
                    + "with multiplier exp(−48a). Extending each positive majorant to the whole "
                    + "positive half-line gives r to the power −(k+1) by the Gamma integral.")),
                Paragraph(Text("The inequalities 640a−1 ≤ k ≤ 640a and the elementary logarithmic "
                    + "bounds absorb the two multipliers. The left and right contributions are at "
                    + "most M times 512 to the power −k divided by 542 and 478 respectively."))),
            DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var a = F.Id("a");
        var u = F.Id("u");
        var k = F.Id("k");
        var g = F.Id("g");
        var m = F.Id("M");
        var f = F.Id("f");
        var s = F.Id("S");
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var hypothesis = All("u", real, Implies(Le(F.D(0), u),
            Le(new Formula.Absolute(new Formula.Apply(g, [u])), Multiply(m, Call("exp", Multiply(F.D(2), u))))));
        var mass = F.Seq(F.Int, F.Underscore, F.Grp(s), F.Sp, new Formula.Apply(f, [u]),
            F.Sp, F.Id("d"), u);
        var constant = Add(new Formula.Fraction(F.D(1), F.D(5,4,2)),
            new Formula.Fraction(F.D(1), F.D(4,7,8)));
        var bound = Multiply(Multiply(m, constant), new Formula.Power(F.D(5,1,2), new Formula.Negate(k)));
        return F.Disp(All("a", real, Implies(Le(F.D(1), a),
            All("g", new Formula.TypeArrow(real, real), Implies(Call("Measurable", g),
                All("M", real, Implies(hypothesis,
                    And(Le(a, k), And(Call("IntegrableOn", f, s), Le(mass, bound))))))))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
