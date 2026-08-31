using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenScaleCircleDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden logarithmic scale turns multiplication into translation and multiplication by phi squared into one full shell step.",
        H("Golden Scale Circle"),
        Blocks(
            Theorem("golden-scale-period-pos", "golden_scale_period_pos",
                "The Golden Scale Period Is Positive", GoldenScalePeriodPosFormula(),
                "Twice the logarithm of the golden ratio is strictly positive because the golden ratio exceeds one.",
                "This establishes the sign of the chosen orientation-preserving period; it makes no statement about a quotient coordinate."),
            Theorem("golden-scale-period-ne-zero", "golden_scale_period_ne_zero",
                "The Golden Scale Period Is Nonzero", GoldenScalePeriodNeZeroFormula(),
                "Strict positivity immediately rules out a zero golden scale period.",
                "The conclusion records only the nonvanishing needed for later divisions by the period."),
            Theorem("golden-scale-coordinate-mul", "golden_scale_coordinate_mul",
                "Positive Multiplication Becomes Coordinate Addition", GoldenScaleCoordinateMulFormula(),
                "For positive real scales, the logarithm of a product splits into the sum of the two logarithms.",
                "Dividing by the common golden period gives exact additivity on the unwrapped coordinate, without passing to a circle quotient."),
            Theorem("log-golden-ratio-sq-eq-period", "log_golden_ratio_sq_eq_period",
                "The Golden Square Has One Full Logarithmic Period", LogGoldenRatioSqEqPeriodFormula(),
                "The logarithm of the square of the golden ratio is twice its logarithm and hence equals the defined scale period.",
                "This is an exact normalization identity, not an approximation to the golden ratio or its logarithm."),
            Theorem("golden-scale-coordinate-phi-sq-mul", "golden_scale_coordinate_phi_sq_mul",
                "Multiplication by Phi Squared Advances One Shell", GoldenScaleCoordinatePhiSqMulFormula(),
                "Multiplying a positive scale by the square of the golden ratio adds its one-period coordinate.",
                "The result concerns the real-valued lift and asserts a translation by one, not equality after quotienting by integers."),
            Theorem("golden-scale-coordinate-phi-even-pow-mul", "golden_scale_coordinate_phi_even_pow_mul",
                "Even Golden Powers Advance by a Natural Number of Shells", GoldenScaleCoordinatePhiEvenPowMulFormula(),
                "Iterating multiplication by the orientation-preserving golden unit advances the coordinate by the natural exponent.",
                "The positivity hypothesis on the base scale remains explicit, and the conclusion is limited to natural iterations."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula GoldenScalePeriodPosFormula() =>
        Statement([], [], Seq(D(0), Sp, Lt, Sp, F.Id("goldenScalePeriod")));

    private static Formula GoldenScalePeriodNeZeroFormula() =>
        Statement([], [], Seq(F.Id("goldenScalePeriod"), Sp, Neq, Sp, D(0)));

    private static Formula GoldenScaleCoordinateMulFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Statement([Typed(x, Reals()), Typed(y, Reals())],
            [Positive(x), Positive(y)],
            Seq(Call("goldenScaleCoordinate", Product(x, y)), Sp, Eq, Sp,
                Call("goldenScaleCoordinate", x), Sp, Plus, Sp,
                Call("goldenScaleCoordinate", y)));
    }

    private static Formula LogGoldenRatioSqEqPeriodFormula() =>
        Statement([], [], Seq(Call("log", Pow(Varphi, D(2))), Sp, Eq, Sp,
            F.Id("goldenScalePeriod")));

    private static Formula GoldenScaleCoordinatePhiSqMulFormula()
    {
        Formula x = F.Id("x");
        return Statement([Typed(x, Reals())], [Positive(x)],
            Seq(Call("goldenScaleCoordinate", Product(Pow(Varphi, D(2)), x)),
                Sp, Eq, Sp, Call("goldenScaleCoordinate", x), Sp, Plus, Sp, D(1)));
    }

    private static Formula GoldenScaleCoordinatePhiEvenPowMulFormula()
    {
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula iteratedUnit = Pow(Pow(Varphi, D(2)), n);
        return Statement([Typed(n, Naturals()), Typed(x, Reals())], [Positive(x)],
            Seq(Call("goldenScaleCoordinate", Product(iteratedUnit, x)),
                Sp, Eq, Sp, Call("goldenScaleCoordinate", x), Sp, Plus, Sp,
                Coerce(n, Reals())));
    }

    private static Formula Statement(Formula[] binders, Formula[] hypotheses, Formula conclusion)
    {
        List<Formula> items = [];
        if (binders.Length > 0)
        {
            items.Add(Forall); items.Add(Sp); AddSeparated(items, binders, Comma);
            items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        }
        if (hypotheses.Length > 0)
        {
            AddSeparated(items, hypotheses.Select(h => Seq(Open, h, Close)).ToArray(), Land);
            items.Add(Sp); items.Add(Rightarrow); items.Add(RowBreak); items.Add(Grp());
        }
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static void AddSeparated(List<Formula> items, Formula[] values, Formula separator)
    {
        for (int index = 0; index < values.Length; index++)
        {
            if (index > 0) { items.Add(Sp); items.Add(separator); items.Add(Sp); }
            items.Add(values[index]);
        }
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Positive(Formula value) => Seq(D(0), Sp, Lt, Sp, value);
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Pow(Formula value, Formula exponent) => Seq(Grp(value), Caret, Grp(exponent));
    private static Formula Coerce(Formula value, Formula type) => Seq(Open, value, Colon, Sp, type, Close);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
