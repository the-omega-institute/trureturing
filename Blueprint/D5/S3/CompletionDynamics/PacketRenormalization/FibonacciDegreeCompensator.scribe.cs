using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.PacketRenormalization;

internal sealed class FibonacciDegreeCompensatorDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/CompletionDynamics/PacketRenormalization/FibonacciDegreeCompensator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even Fibonacci degrees compensate the inverse-square golden contraction.",
        H("Fibonacci Degree Compensator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-renormalization"),
                DeclarationHandle.Create(Prefix + "goldenRenormalization"),
                H("Golden renormalization"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("R"), Underscore, Grp(Varphi), Open, Delta, Close,
                    Sp, Eq, Sp,
                    Varphi, Caret, Grp(Minus, D(2)), Delta, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One golden renormalization step contracts a real transverse defect by "
                        + "the inverse square of the golden ratio."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibonacci-degree"),
                DeclarationHandle.Create(Prefix + "fibonacciDegree"),
                H("Even Fibonacci degree"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("D"), Underscore, Grp(F.Id("r")), Open, F.Id("n"), Close,
                    Sp, Eq, Sp,
                    F.Id("F"), Underscore,
                    Grp(D(2), F.Id("n"), Plus, F.Id("r")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At step n and natural offset r, the integer observation degree is the "
                        + "Fibonacci number with index 2n+r."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-compensator"),
                DeclarationHandle.Create(Prefix + "IsIntegerCompensator"),
                H("Integer compensator"),
                StatementSource.FromAuthor(CompensatorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A natural-valued degree sequence compensates a real renormalization when, "
                        + "for every initial defect, the degree-orbit product converges to that "
                        + "initial value multiplied by the prescribed gain."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibonacci-degree-compensator"),
                DeclarationHandle.Create(Prefix + "fibonacci_degree_compensator"),
                H("Fibonacci degrees compensate golden contraction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the source sequences satisfy N(n)=F(2n+r) and "
                            + "delta(n)=delta-zero times phi to the power -2n. The theorem "
                            + "then exposes both displayed limits as separate conclusions.")),
                    Paragraph(Text(
                        "Its third conclusion states the final structural clause: the actual "
                            + "even Fibonacci degree sequence is an integer compensator for "
                            + "inverse-square golden renormalization, uniformly over its real "
                            + "initial defect."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula Limit(Formula index, Formula expression, Formula value) =>
        Seq(Lim, Underscore, Grp(index, To, Infty), Sp, expression, Sp, Eq, Sp, value);

    private static Formula CompensatorFormula()
    {
        Formula renormalization = F.Id("R");
        Formula degree = F.Id("D");
        Formula gain = F.Id("g");
        Formula initial = F.Id("a");
        Formula step = F.Id("n");
        Formula orbit = Call("iterate", renormalization, step, initial);
        Formula product = Seq(degree, Open, step, Close, Sp, orbit);
        Formula target = Seq(initial, Sp, gain);

        return Disp(Seq(
            Call("IsIntegerCompensator", renormalization, degree, gain), Sp, Iff, Sp,
            Forall, Sp, initial, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
            Limit(step, product, target), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula r = F.Id("r");
        Formula n = F.Id("n");
        Formula initial = Seq(Delta, Underscore, Grp(D(0)));
        Formula degree = F.Id("N");
        Formula defect = Delta;
        Formula fibIndex = Seq(D(2), n, Plus, r);
        Formula fib = Seq(F.Id("F"), Underscore, Grp(fibIndex));
        Formula phiScale = new Formula.Power(Varphi, Seq(Minus, D(2), n));
        Formula gain = Seq(
            Frac, Grp(new Formula.Power(Varphi, r)), Grp(Sqrt, Grp(D(5))));
        Formula normalized = Seq(fib, Sp, phiScale);
        Formula product = Seq(
            degree, Underscore, Grp(n), Sp, defect, Underscore, Grp(n));
        Formula productTarget = Seq(initial, Sp, gain);

        Formula degreePremise = Seq(
            Forall, Sp, n, InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
            degree, Underscore, Grp(n), Sp, Eq, Sp, fib);
        Formula defectPremise = Seq(
            Forall, Sp, n, InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
            defect, Underscore, Grp(n), Sp, Eq, Sp, initial, Sp, phiScale);
        Formula conclusions = And(
            Limit(n, normalized, gain),
            And(
                Limit(n, product, productTarget),
                Call(
                    "IsIntegerCompensator",
                    F.Id("goldenRenormalization"),
                    Call("fibonacciDegree", r),
                    gain)));

        return Disp(Seq(
            Forall, Sp, r, InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Forall, Sp, initial, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
            Forall, Sp, degree, Colon, Mathbb, Grp(F.Id("N")), To,
                Mathbb, Grp(F.Id("N")), Comma, Esc,
            Forall, Sp, defect, Colon, Mathbb, Grp(F.Id("N")), To,
                Mathbb, Grp(F.Id("R")), Comma, Esc,
            Implies(
                Seq(Open, degreePremise, Close),
                Implies(Seq(Open, defectPremise, Close), conclusions)),
            Dot));
    }
}
