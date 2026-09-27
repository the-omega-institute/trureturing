using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class ProbeThresholdOptimizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/ErrorExponents/ProbeThresholdOptimization."
            + "probe_threshold_optimization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive probability vector has a unique threshold, a capped quadratic optimizer, and an exact active-set value.",
        H("Probe Threshold Optimization"),
        Blocks(Describe.Lean(
            DescribeId.Create("probe-threshold-optimization"),
            DeclarationHandle.Create(Declaration),
            H("The probe threshold is unique and globally optimal"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The threshold balances the capped square-root weights against epsilon. "
                        + "Strict decrease after the uncapped range makes this balance unique.")),
                Paragraph(Text(
                    "Linearizing the squared aggregate separates the box optimization by coordinate. "
                        + "Each coordinate is maximized by its capped linear response.")),
                Paragraph(Text(
                    "Splitting the coordinates at the cap gives the threshold identity and the exact "
                        + "objective value in terms of the active mass, active square-root sum, and active count."))),
            DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Open, source, Close, Sp, To, Sp, target);

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Minimum(Formula left, Formula right) =>
        Seq(Min, Open, left, Comma, Sp, right, Close);

    private static Formula SumAt(Formula index, Formula value) =>
        Seq(Sum, Underscore, Grp(index), Sp, value);

    private static Formula TheoremFormula()
    {
        Formula iota = Iota, l = F.Id("l"), a = F.Id("a"), epsilon = Varepsilon;
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula v = F.Id("v"), objective = F.Id("F"), x = F.Id("x");
        Formula cPrime = Seq(F.Id("c"), Apos);
        Formula threshold = F.Id("c"), active = F.Id("H");
        Formula inactiveMass = F.Id("d"), activeSum = F.Id("S");
        Formula xStar = Subscript(x, Star);
        Formula aAt = Subscript(a, l), vAt = Subscript(v, l);
        Formula xAt = Subscript(x, l), xStarAt = Subscript(Grp(xStar), l);
        Formula vectorType = Arrow(iota, real);
        Formula sumA = SumAt(l, aAt);
        Formula aggregate = SumAt(l, Seq(vAt, Sp, Cdot, Sp, xAt));
        Formula normSquare = SumAt(l, Power(xAt, D(2)));
        Formula objectiveAtX = Seq(
            At(objective, x), Sp, Eq, Sp,
            Open, Power(Seq(Open, aggregate, Close), D(2)), Sp, Minus, Sp,
            epsilon, Sp, Cdot, Sp, normSquare, Close);
        Formula vDefinition = Seq(
            v, Sp, Eq, Sp,
            Open, l, Colon, Sp, iota, Sp, Mapsto, Sp, Sqrt, Grp(aAt), Close);
        Formula xStarDefinition = Seq(
            xStar, Sp, Eq, Sp,
            Open, l, Colon, Sp, iota, Sp, Mapsto, Sp,
            Minimum(D(1), Seq(threshold, Sp, Cdot, Sp, vAt)), Close);
        Formula activeDefinition = Seq(
            active, Sp, Eq, Sp, OpenBrace, l, Sp, Mid, Sp,
            D(1), Sp, Le, Sp, threshold, Sp, Cdot, Sp, vAt, CloseBrace);
        Formula inactiveDefinition = Seq(
            inactiveMass, Sp, Eq, Sp, Sum, Underscore,
            Grp(l, Sp, InMacro, Sp, iota, Sp, Setminus, Sp, active), Sp, aAt);
        Formula activeSumDefinition = Seq(
            activeSum, Sp, Eq, Sp, Sum, Underscore,
            Grp(l, Sp, InMacro, Sp, active), Sp, vAt);
        Formula coordinateBounds = Seq(
            Open, Forall, Sp, l, Comma, Sp, Open,
            D(0), Sp, Le, Sp, xStarAt, Sp, Land, Sp, xStarAt, Sp, Le, Sp, D(1),
            Close, Close);
        Formula arbitraryBounds = Seq(
            Open, Forall, Sp, l, Comma, Sp, Open,
            D(0), Sp, Le, Sp, xAt, Sp, Land, Sp, xAt, Sp, Le, Sp, D(1),
            Close, Close);
        Formula rootEquation = Seq(
            SumAt(l, Minimum(aAt, Fraction(vAt, threshold))),
            Sp, Eq, Sp, epsilon);
        Formula rootEquationPrime = Seq(
            SumAt(l, Minimum(aAt, Fraction(vAt, cPrime))),
            Sp, Eq, Sp, epsilon);
        Formula maximumClause = Seq(
            Open, Forall, Sp, Typed(x, vectorType), Comma, Sp,
            Open, arbitraryBounds, Close, Sp, Rightarrow, Sp,
            Open, At(objective, x), Sp, Le, Sp, At(objective, xStar), Close, Close);
        Formula rootUniqueness = Seq(
            Open, Forall, Sp, Typed(cPrime, real), Comma, Sp,
            Open, D(0), Sp, Lt, Sp, cPrime, Close, Sp, Rightarrow, Sp,
            Open, rootEquationPrime, Close, Sp, Rightarrow, Sp,
            Open, cPrime, Sp, Eq, Sp, threshold, Close, Close);
        Formula thresholdFormula = Seq(
            threshold, Sp, Eq, Sp,
            Fraction(activeSum, Seq(epsilon, Sp, Minus, Sp, inactiveMass)));
        Formula valueFormula = Seq(
            At(objective, xStar), Sp, Eq, Sp,
            Fraction(
                Seq(epsilon, Sp, Cdot, Sp, Power(activeSum, D(2))),
                Seq(epsilon, Sp, Minus, Sp, inactiveMass)),
            Sp, Minus, Sp, Open, epsilon, Sp, Cdot, Sp,
            Operatorname, Grp(F.Id("card")), Open, active, Close, Close);
        Formula hypotheses = Seq(
            Open,
            Open, Forall, Sp, l, Comma, Sp,
            Open, D(0), Sp, Lt, Sp, aAt, Close, Close,
            Sp, Land, Sp, Open, sumA, Sp, Eq, Sp, D(1), Close,
            Sp, Land, Sp, Open, D(0), Sp, Lt, Sp, epsilon, Sp, Land, Sp,
            epsilon, Sp, Lt, Sp, D(1), Close,
            Close);
        Formula property = Seq(
            Open, D(0), Sp, Lt, Sp, threshold, Close, Sp, Land, Sp,
            Open, rootEquation, Close, Sp, Land, Sp,
            Open, xStarDefinition, Close, Sp, Land, Sp,
            Open, activeDefinition, Close, Sp, Land, RowBreak,
            Open, inactiveDefinition, Close, Sp, Land, Sp,
            Open, activeSumDefinition, Close, Sp, Land, RowBreak,
            Open, coordinateBounds, Close, Sp, Land, RowBreak,
            Open, maximumClause, Close, Sp, Land, RowBreak,
            Open, inactiveMass, Sp, Lt, Sp, epsilon, Close, Sp, Land, RowBreak,
            Open, thresholdFormula, Close, Sp, Land, RowBreak,
            Open, valueFormula, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(iota, Seq(Operatorname, Grp(F.Id("Type")))), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, iota, Close,
            CloseBracket, RowBreak, Grp(),
            Forall, Sp, Typed(a, vectorType), Comma, Sp, Typed(epsilon, real), Comma, RowBreak, Grp(),
            hypotheses, Sp, Rightarrow, RowBreak, Grp(),
            Open, vDefinition, Close, Comma, Sp,
            Open, objectiveAtX, Close, Comma, RowBreak, Grp(),
            Exists, Sp, Typed(threshold, real), Comma, Sp,
            Open, property, Close, Sp, Land, Sp, rootUniqueness, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
