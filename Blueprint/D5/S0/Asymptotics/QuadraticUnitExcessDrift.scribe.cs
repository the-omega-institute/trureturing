using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class QuadraticUnitExcessDriftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal excess identity determines the quadratic-unit drift slope exactly.",
        H("Quadratic-Unit Excess Drift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-unit-excess-drift-formula-and-zero-criterion"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/QuadraticUnitExcessDrift."
                        + "quadratic_unit_excess_drift"),
                H("The excess identity fixes the drift and its reciprocal zero criterion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the reciprocal excess law for positive x and the drift "
                            + "antisymmetry s(x inverse) = -s(x). At a real unit epsilon greater "
                            + "than one, suppose epsilon plus its inverse is 2t and the paired V "
                            + "values cancel. Substitution into the excess law and division by the "
                            + "positive log epsilon give the displayed closed slope.")),
                    Paragraph(Text(
                        "If a reciprocal orbit also preserves the drift, preservation and "
                            + "antisymmetry give s(x) = -s(x), hence s(x) = 0. This is the exact "
                            + "algebraic content needed by the norm-minus-one criterion.")),
                    Paragraph(Text(
                        "The source statement was tightened by making epsilon > 1 explicit. Lean's "
                            + "Real.log is total and equals zero at one, so this condition is needed "
                            + "for the division in the slope formula. The analytic construction of V "
                            + "and the Cesaro-Abel convergence assertions are inputs, not re-proved "
                            + "by this algebraic closure."))),
                DescribeRole.Theorem)),
        []));

    private static Formula TheoremFormula()
    {
        Formula epsilon = F.Id("epsilon");
        Formula t = F.Id("t");
        Formula x = F.Id("x");
        Formula inverseEpsilon = Power(epsilon, F.Seq(F.Minus, F.D(1)));
        Formula inverseX = Power(x, F.Seq(F.Minus, F.D(1)));
        Formula excessLaw = F.Seq(
            F.Forall, F.Sp, x, F.Gt, F.D(0), F.Comma, F.Sp,
            Call("V", x), F.Sp, F.Plus, F.Sp, Call("V", inverseX), F.Sp, F.Eq, F.Sp,
            Fraction(F.Pi, F.D(6)), F.Sp, F.Times, F.Sp,
            F.Grp(x, F.Sp, F.Plus, F.Sp, inverseX), F.Sp, F.Minus, F.Sp,
            Fraction(F.Pi, F.D(2)), F.Sp, F.Plus, F.Sp,
            Call("s", x), F.Sp, F.Times, F.Sp, F.Log, F.Sp, x);
        Formula reciprocalLaw = F.Seq(
            F.Forall, F.Sp, x, F.Gt, F.D(0), F.Comma, F.Sp,
            Call("s", inverseX), F.Sp, F.Eq, F.Sp, F.Minus, Call("s", x));
        Formula traceAndCancellation = F.Seq(
            epsilon, F.Gt, F.D(1), F.Comma, F.Sp,
            epsilon, F.Sp, F.Plus, F.Sp, inverseEpsilon, F.Sp, F.Eq, F.Sp,
            F.D(2), F.Times, F.Sp, t, F.Comma, F.Sp,
            Call("V", epsilon), F.Sp, F.Plus, F.Sp, Call("V", inverseEpsilon),
            F.Sp, F.Eq, F.Sp, F.D(0));
        Formula slope = F.Seq(
            Call("s", epsilon), F.Sp, F.Eq, F.Sp, F.Minus,
            Fraction(
                F.Seq(F.Pi, F.Sp, F.Times, F.Sp,
                    F.Grp(F.D(2), F.Times, F.Sp, t, F.Sp, F.Minus, F.Sp, F.D(3))),
                F.Seq(F.D(6), F.Sp, F.Times, F.Sp, F.Log, F.Sp, epsilon)));
        Formula zeroCriterion = F.Seq(
            F.Forall, F.Sp, x, F.Gt, F.D(0), F.Comma, F.Sp,
            Call("s", inverseX), F.Sp, F.Eq, F.Sp, Call("s", x),
            F.Sp, F.Rightarrow, F.Sp, Call("s", x), F.Sp, F.Eq, F.Sp, F.D(0));

        return F.Disp(new Formula.Aligned([
            F.Seq(excessLaw, F.Comma),
            F.Seq(reciprocalLaw, F.Comma),
            F.Seq(traceAndCancellation, F.Sp, F.Rightarrow),
            F.Seq(slope, F.Sp, F.Land, F.Sp, zeroCriterion, F.Dot),
        ]));
    }

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
