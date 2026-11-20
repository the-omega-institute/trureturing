using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CompleteMangoldtAtOneDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cauchy bounds after removing a zeta pole from the complete Mangoldt transform",
        H("Cauchy estimates for the completed Mangoldt transform"),
        Blocks(
            Describe.Lean(DescribeId.Create("completed"), DeclarationHandle.Create(Module + "completed"),
                H("The completed transform"), StatementSource.FromAuthor(F.Disp(Definition())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Write T for the explicit complete Mangoldt transform, h for the entire normalized zeta "
                    + "function, and A for its logarithmic derivative. Away from 1, h(s)=(s−1)ζ(s). "
                    + "At 1 its value is 1 and its derivative is Euler's constant γ. "
                    + "Thus A(1)=γ. The completed transform is denoted by F."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniqueness"), DeclarationHandle.Create(Module + "completed_disk_cauchy"),
                H("The unique fill and its single-pole Cauchy estimate"), StatementSource.FromAuthor(F.Disp(Claim())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The original rational expression on the punctured neighborhood of 1 equals "
                        + "[1+γ−(A(s)−A(1))/(s−1)]/s. The term 1/(s−1) in the negative logarithmic "
                        + "derivative cancels the double pole after these fractions are combined. "
                        + "The divided difference extends analytically with value A′(1).")),
                    Paragraph(Text("At every other nonzero point with ζ(s) nonzero, the ordinary quotient "
                        + "rules give analyticity. Equality to T off 1 preserves its half-plane integral and "
                        + "its punctured expansions at the zeta zeros. Continuity at 1 forces the same "
                        + "limit for any other function agreeing with T everywhere else.")),
                    Paragraph(Text("Let p be the center and r the radius of the closed disk. The disk excludes 0 "
                        + "and every zeta zero other than the selected zero z. The center differs from z. "
                        + "The disk may contain 1 and may include z in its interior or on its boundary. "
                        + "Write c(z)=m/[z(1−z)] for the residue, where m is the order of ζ at z.")),
                    Paragraph(Text("Subtract c(z)/(s−z) from F(s). At z assign to the difference the value of the "
                        + "analytic local Laurent remainder. This yields a single function analytic near every "
                        + "point of the disk, including 1. Its supremum on the circle bounds every Taylor "
                        + "coefficient at p by the Cauchy estimate. The derivative of the subtracted pole contributes "
                        + "the term c(z)(−1)ⁿn!/(p−z)ⁿ⁺¹."))), DescribeRole.Theorem))));

    private static Formula Complex => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula ComplexFunction => F.Seq(F.Open, Complex, F.Sp, F.To, F.Sp, Complex, F.Close);
    private static Formula At(string name, Formula s) =>
        new Formula.Apply(F.Id(name), [s]);
    private static Formula Equal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Unequal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula If(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Predicate(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula OffOne(string name)
    {
        var s = F.Id("s");
        return All("s", Complex, If(Unequal(s, F.D(1)), Equal(At(name, s), At("T", s))));
    }

    private static Formula Definition()
    {
        var derivative = new Formula.Apply(F.Seq(F.Id("A"), F.Apos), [F.D(1)]);
        return And(OffOne("F"), Equal(At("F", F.D(1)), Subtract(Add(F.D(1), F.GammaLower), derivative)));
    }

    private static Formula Claim()
    {
        var s = F.Id("s");
        var f = F.Id("F");
        var g = F.Id("G");
        var analytic = All("s", Complex, If(And(Unequal(s, F.D(0)),
            Unequal(new Formula.Apply(F.Zeta, [s]), F.D(0))), Predicate("AnalyticAt", Complex, f, s)));
        var unique = All("G", ComplexFunction, If(And(Predicate("ContinuousAt", g, F.D(1)), OffOne("G")),
            Equal(g, f)));
        return And(And(Definition(), And(analytic, unique)), Disk());
    }

    private static Formula Disk()
    {
        var p = F.Id("p");
        var z = F.Id("z");
        var w = F.Id("w");
        var r = F.Id("r");
        var n = F.Id("n");
        var b = F.Id("B");
        var zero = F.D(0);
        var real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var nat = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var disk = new Formula.Relation(w, FormulaRelationOperator.MemberOf, Predicate("closedBall", p, r));
        var allPoints = All("w", Complex, If(disk, And(Unequal(w, zero),
            If(Equal(new Formula.Apply(F.Zeta, [w]), zero), Equal(w, z)))));
        var hypotheses = And(new Formula.Relation(zero, FormulaRelationOperator.LessThan, r),
            And(Unequal(p, z), And(Equal(new Formula.Apply(F.Zeta, [z]), zero), allPoints)));
        var factorial = Predicate("factorial", n);
        var correction = new Formula.Fraction(Multiply(Predicate("c", z),
            Multiply(new Formula.Power(new Formula.Negate(F.D(1)), n), factorial)),
            new Formula.Power(Subtract(p, z), Add(n, F.D(1))));
        var error = new Formula.Absolute(Subtract(Predicate("iteratedDeriv", n, F.Id("F"), p), correction));
        var bound = new Formula.Relation(error, FormulaRelationOperator.LessThanOrEqual,
            new Formula.Fraction(Multiply(factorial, b), new Formula.Power(r, n)));
        var conclusion = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("B"), real,
            And(new Formula.Relation(zero, FormulaRelationOperator.LessThanOrEqual, b), All("n", nat, bound)));
        return All("p", Complex, All("z", Complex, All("r", real, If(hypotheses, conclusion))));
    }
}
