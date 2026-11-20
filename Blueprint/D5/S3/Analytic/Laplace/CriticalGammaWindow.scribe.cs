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
        var order = new Formula.Floor(Multiply(F.D(6,4,0), a));
        var rightEndpoint = new Formula.Fraction(Multiply(F.D(3), a), F.D(2));
        var outside = F.Seq(F.Open, F.D(0), F.Comma, F.Infty, F.Close, F.Sp, F.Setminus, F.Sp,
            F.OpenBracket, a, F.Comma, rightEndpoint, F.CloseBracket);
        var density = Multiply(new Formula.Absolute(new Formula.Apply(g, [u])),
            new Formula.Fraction(Multiply(new Formula.Power(u, k),
                Call("exp", new Formula.Negate(Multiply(F.D(5,1,2), u)))), F.Seq(k, F.Bang)));
        var conclusion = new Formula.Aligned([
            Let(k, order),
            Let(f, F.Seq(F.Open, u, F.Sp, F.Mapsto, F.Sp, density, F.Close)),
            Let(s, outside),
            And(Le(a, k), And(Call("IntegrableOn", f, s), Le(mass, bound))),
        ]);
        return F.Disp(All("a", real, Implies(Le(F.D(1), a),
            All("g", new Formula.TypeArrow(real, real), Implies(Call("Measurable", g),
                All("M", real, Implies(hypothesis, conclusion)))))));
    }

    private static Formula Let(Formula name, Formula value) =>
        F.Seq(F.Operatorname, F.Grp(F.Id("let")), F.Sp, name, F.Sp, F.Colon, F.Eq, F.Sp, value, F.Comma);
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
