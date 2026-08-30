using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HolonomyDeterminant;

internal sealed class MasslessHolonomyDeterminantDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/HolonomyDeterminant/MasslessHolonomyDeterminant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reflected massless holonomy zeta has a scale-free sine determinant.",
        H("Massless Holonomy Determinant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("holonomy-hurwitz-sum-at-zero"),
                DeclarationHandle.Create(Prefix + "holonomy_hurwitz_sum_at_zero"),
                H("The reflected Hurwitz sum vanishes at zero"),
                StatementSource.FromAuthor(HurwitzSumAtZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a holonomy strictly between zero and one, the two reflected Hurwitz "
                        + "sectors form twice the even Hurwitz zeta value, which is zero at the "
                        + "origin."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("holonomy-determinant-scale-invariant"),
                DeclarationHandle.Create(Prefix + "holonomy_determinant_scale_invariant"),
                H("The determinant is independent of an overall scale"),
                StatementSource.FromAuthor(ScaleInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Differentiating the exponential scale factor produces a term multiplied "
                        + "by the reflected zeta value at zero. The preceding vanishing result "
                        + "therefore removes it for every real scale parameter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("massless-holonomy-determinant"),
                DeclarationHandle.Create(Prefix + "massless_holonomy_determinant"),
                H("The massless determinant is the sine chord"),
                StatementSource.FromAuthor(DeterminantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assuming the reflected Lerch derivative formula missing from the pinned "
                        + "library, Euler reflection converts the zeta derivative to the "
                        + "dimensionless value two times sine of pi alpha."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("holonomy-sine-eq-chord-length"),
                DeclarationHandle.Create(Prefix + "holonomy_sine_eq_chord_length"),
                H("The sine value is the unit-circle chord length"),
                StatementSource.FromAuthor(ChordLengthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For alpha in the closed unit interval, the norm of the difference from "
                        + "one to the unit-circle point with angle two pi alpha is exactly two "
                        + "times sine of pi alpha."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chord-interval-is-necessary"),
                DeclarationHandle.Create(Prefix + "chord_interval_is_necessary"),
                H("The chord identity needs both interval bounds"),
                StatementSource.FromAuthor(ChordIntervalWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At alpha minus one half and three halves, the sine expression is negative "
                        + "while the norm defining the chord is positive. The two concrete "
                        + "witnesses separately cross the lower and upper bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("holonomy-interval-is-necessary"),
                DeclarationHandle.Create(Prefix + "holonomy_interval_is_necessary"),
                H("Both interval endpoints violate the sine formula"),
                StatementSource.FromAuthor(IntervalWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At alpha zero and one the sine side vanishes, while a complex exponential "
                        + "is never zero. These named endpoint witnesses justify excluding both "
                        + "boundaries."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("derivative-formula-is-necessary"),
                DeclarationHandle.Create(Prefix + "derivative_formula_is_necessary"),
                H("Vanishing at zero alone does not determine the determinant"),
                StatementSource.FromAuthor(DerivativeWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constant-zero mock zeta vanishes at zero but has regularized "
                        + "determinant one, not the value two obtained at alpha one half. Thus "
                        + "derivative data cannot be replaced by zero-value data alone."))),
                DescribeRole.Theorem))));

    private static Formula HurwitzSumAtZeroFormula()
    {
        Formula alpha = Alpha;
        return Disp(ForEvery(
            [Bound("alpha", Reals())],
            Implies(InOpenUnitInterval(alpha),
                EqualTo(Call("holonomyHurwitzSum", alpha, D(0)), D(0)))));
    }

    private static Formula ScaleInvariantFormula()
    {
        Formula alpha = Alpha;
        Formula scale = F.Id("scale");
        Formula sum = Call("holonomyHurwitzSum", alpha);
        Formula scaled = Call("scaledSpectralZeta", scale, sum);
        return Disp(ForEvery(
            [Bound("alpha", Reals()), Bound("scale", Reals())],
            Implies(
                InOpenUnitInterval(alpha),
                EqualTo(
                    Call("zetaRegularizedDeterminant", scaled),
                    Call("masslessHolonomyDeterminant", alpha)))));
    }

    private static Formula DeterminantFormula()
    {
        Formula alpha = Alpha;
        Formula premise = And(
            InOpenUnitInterval(alpha),
            Call("HasReflectedHurwitzDerivativeAtZeroFormula", alpha));
        return Disp(ForEvery(
            [Bound("alpha", Reals())],
            Implies(
                premise,
                EqualTo(
                    Call("masslessHolonomyDeterminant", alpha),
                    SineChord(alpha)))));
    }

    private static Formula IntervalWitnessFormula()
    {
        Formula atZero = NotEqualTo(
            Call("masslessHolonomyDeterminant", D(0)),
            SineChord(D(0)));
        Formula atOne = NotEqualTo(
            Call("masslessHolonomyDeterminant", D(1)),
            SineChord(D(1)));
        return Disp(And(atZero, atOne));
    }

    private static Formula ChordLengthFormula()
    {
        Formula alpha = Alpha;
        Formula closedInterval = And(
            LessThanOrEqual(D(0), alpha),
            LessThanOrEqual(alpha, D(1)));
        return Disp(ForEvery(
            [Bound("alpha", Reals())],
            Implies(
                closedInterval,
                EqualTo(Call("holonomyChordLength", alpha), SineChord(alpha)))));
    }

    private static Formula ChordIntervalWitnessFormula()
    {
        Formula negativeHalf = Seq(Minus, new Formula.Fraction(D(1), D(2)));
        Formula threeHalves = new Formula.Fraction(D(3), D(2));
        return Disp(And(
            NotEqualTo(
                Call("holonomyChordLength", negativeHalf),
                SineChord(negativeHalf)),
            NotEqualTo(
                Call("holonomyChordLength", threeHalves),
                SineChord(threeHalves))));
    }

    private static Formula DerivativeWitnessFormula()
    {
        Formula zeroZeta = F.Id("zeroZeta");
        Formula half = new Formula.Fraction(D(1), D(2));
        return Disp(And(
            EqualTo(Call("zeroZeta", D(0)), D(0)),
            NotEqualTo(
                Call("zetaRegularizedDeterminant", zeroZeta),
                SineChord(half))));
    }

    private static Formula SineChord(Formula alpha) =>
        Seq(D(2), Sp, Times, Sp, Call("sin", Seq(Pi, Sp, Times, Sp, alpha)));

    private static Formula InOpenUnitInterval(Formula value) =>
        And(LessThan(D(0), value), LessThan(value, D(1)));

    private static Formula ForEvery(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
