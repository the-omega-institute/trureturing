using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MomentMinors;

internal sealed class BoundedFifthMomentLimitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/StatisticalMechanics/meerweeks2024boundedmoments");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fifth central moment inequalities for probability laws bounded on one side.",
        H("One-sided fifth moment bounds"), Blocks(
            Describe.Lean(
                DescribeId.Create("fifth-bound"),
                DeclarationHandle.Create(Module + ".fifthBound"),
                H("The two-point fifth moment expression"),
                StatementSource.FromAuthor(Disp(FifthBoundFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The function fifthBound is the real expression z³ − z + z⁻¹ − (z⁻¹)³. "
                    + "For positive z it is the standardized fifth moment of the two-point law "
                    + "whose ratio of standard deviation to distance from the lower endpoint to "
                    + "the mean is z. Its definition also assigns a value at zero using the real "
                    + "inverse, for which the inverse of zero is zero. The expression occurs in "
                    + "Meer and Weeks, arXiv:2308.05006v2, plos_latex_template.tex, lines 500–510."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The two one-sided inequalities"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimFormula()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The proposition concerns every Borel probability measure μ on the real line "
                    + "with integrable fifth absolute moment and strictly positive variance. "
                    + "For every almost sure lower bound L, the standardized fifth central moment "
                    + "is at least fifthBound at the ratio of standard deviation to mean μ − L. "
                    + "For every almost sure upper bound U, it is at most the negative of "
                    + "fifthBound at the ratio of standard deviation to U − mean μ. "
                    + "Here mean μ is the integral of x, and centralMoment id k μ is the integral "
                    + "of (x − mean μ)ᵏ. These moments follow the conventions in "
                    + "plos_latex_template.tex, lines 228–236; the ratios are those of "
                    + "lines 397–408, and the fifth moment question is in lines 506–510. "
                    + "The lower and upper bounds are separate implications, so either can be "
                    + "used without assuming a bound on the other side."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Fifth central moment bounds"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First, integrability of |x|⁵ places the identity function in L⁵. "
                        + "Subtracting a real constant c and decreasing the exponent on a "
                        + "probability space shows that (x − c)ᵏ is integrable for every natural "
                        + "k ≤ 5. In particular the first, second and fifth centered powers "
                        + "are integrable.")),
                    Paragraph(Text(
                        "Suppose L ≤ x almost everywhere. The nonnegative integrable function "
                        + "x − L has integral mean μ − L. If this integral were zero, then "
                        + "x − L would vanish almost everywhere, the mean would equal L, and "
                        + "the second central moment would be zero. Positive variance therefore "
                        + "gives a = mean μ − L > 0.")),
                    Paragraph(Text(
                        "For real a, b and y with y ≥ −a, the quadratic "
                        + "Q(y) = y² + (2b − a)y + 3b² − 2ab + a² is nonnegative: "
                        + "it equals (y + b − a/2)² + 2(b − a/4)² + 5a²/8. "
                        + "Consequently R(y) = (y + a)(y − b)²Q(y) is nonnegative. "
                        + "Expanding gives y⁵ − R(y) = Ay² + By + C, where "
                        + "A = −a³ + 2a²b − 3ab² + 4b³, "
                        + "B = 2a³b − 4a²b² + 6ab³ − 3b⁴, and "
                        + "C = −a³b² + 2a²b³ − 3ab⁴. Thus Ay² + By + C ≤ y⁵.")),
                    Paragraph(Text(
                        "Set a = mean μ − L, b = centralMoment id 2 μ / a, "
                        + "and y = x − mean μ. The centered first moment is zero and the "
                        + "centered second moment is ab. The support assumption gives y ≥ −a "
                        + "almost everywhere. Integrating the polynomial inequality is justified "
                        + "by the centered-power integrability above and gives "
                        + "Aab + B·0 + C ≤ centralMoment id 5 μ. The left side simplifies to "
                        + "ab(b − a)(a² + b²).")),
                    Paragraph(Text(
                        "To divide by the standard deviation, put v = centralMoment id 2 μ, "
                        + "M = centralMoment id 5 μ and s = √v. Since v > 0, we have s > 0 "
                        + "and s² = v. Expansion after clearing the nonzero denominators a and s "
                        + "gives fifthBound(s/a)s⁵ = a(v/a)(v/a − a)(a² + (v/a)²). "
                        + "The integrated inequality and s⁵ > 0 now give fifthBound(s/a) ≤ M/s⁵. "
                        + "Together with a > 0 this proves the lower-support implication.")),
                    Paragraph(Text(
                        "For the upper-support implication, let ν be the image of μ under "
                        + "x ↦ −x. Reflection preserves the fifth absolute moment's integrability "
                        + "and gives mean ν = −mean μ. Changing variables in each centered "
                        + "moment gives centralMoment id k ν = (−1)ᵏ centralMoment id k μ. "
                        + "In particular the second central moment is unchanged and the fifth "
                        + "is negated. If x ≤ U almost everywhere for μ, then −U ≤ x almost "
                        + "everywhere for ν. Applying the lower inequality to ν at −U and using "
                        + "mean ν − (−U) = U − mean μ yields the upper inequality for μ. "
                        + "The two implications give the stated conjunction."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("meer-weeks-2024-bounded-fifth-moment-limit"),
                    ResolutionKind.Proved)))));

    private static Formula FifthBoundFormula() => All("z", Reals(),
        Equal(Typed(At(Local("fifthBound"), X("z")), Reals()),
            Subtract(Add(Subtract(Power(X("z"), 3), X("z")), Inverse(X("z"))),
                Power(Inverse(X("z")), 3))));

    private static Formula ClaimFormula()
    {
        Formula variance = Moment(2);
        Formula deviation = At(Qualified("Real", "sqrt"), variance);
        Formula standardized = Divide(Moment(5), Power(deviation, 5));
        Formula lower = All("L", Reals(), Arrow(
            AlmostEverywhere(LessOrEqual(X("L"), X("x"))),
            LessOrEqual(At(Local("fifthBound"),
                Divide(deviation, Subtract(Mean(), X("L")))), standardized)));
        Formula upper = All("U", Reals(), Arrow(
            AlmostEverywhere(LessOrEqual(X("x"), X("U"))),
            LessOrEqual(standardized, new Formula.Negate(Parenthesized(
                At(Local("fifthBound"), Divide(deviation, Subtract(X("U"), Mean()))))))));
        Formula absoluteMoment = At(Qualified("MeasureTheory", "Integrable"),
            LambdaOf("x", Reals(), Power(new Formula.Absolute(X("x")), 5)), Mu);
        return All("μ", At(Qualified("MeasureTheory", "Measure"), Reals()),
            Arrow(At(Qualified("MeasureTheory", "IsProbabilityMeasure"), Mu),
                Arrow(absoluteMoment, Arrow(Less(Typed(D(0), Reals()), variance),
                    Conjunction(lower, upper)))));
    }

    private static Formula Moment(byte k) =>
        At(Qualified("ProbabilityTheory", "centralMoment"), Qualified("id"), D(k), Mu);
    private static Formula Mean() =>
        At(Qualified("D5", "S3", "Analytic", "MomentMinors", "Defs", "mean"), Mu);
    private static Formula AlmostEverywhere(Formula predicate) => At(Qualified("Filter", "Eventually"),
        LambdaOf("x", Reals(), predicate), At(Qualified("MeasureTheory", "ae"), Mu));
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Analytic", "MomentMinors", "BoundedFifthMomentLimit", name);
    private static Formula X(string name) => name == "μ" ? Mu : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Power(Formula value, byte exponent) => new Formula.Power(Parenthesized(value), D(exponent));
    private static Formula Inverse(Formula value) => At(Qualified("Inv", "inv"), value);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
