using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class HermiteMomentBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mean and total squared deviation of positive finite coordinates determine a positive lower Hermite node and an upper node bounding all coordinates.",
        H("Hermite nodes from two moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-strict-square-sum"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/HermiteMomentBounds.sum_sq_lt_sq_sum"),
                H("Strict square-sum inequality"),
                StatementSource.FromAuthor(StrictSquareSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For at least two positive real coordinates, the sum of their squares is strictly less "
                    + "than the square of their sum. For each index i, another index j has a positive "
                    + "coordinate, so Finset.single_lt_sum gives xᵢ < ∑ⱼxⱼ. "
                    + "Multiplying by xᵢ > 0 and summing the strict inequalities gives "
                    + "∑ᵢxᵢ² < ∑ᵢxᵢ(∑ⱼxⱼ) = (∑ᵢxᵢ)²."))),
                DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("hermite-moment-bounds"),
            DeclarationHandle.Create("D5/S3/Analytic/Interpolation/HermiteMomentBounds.hermite_moment_bounds"),
            H("Positive lower node and coordinate upper bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let k be a natural number at least two, and let x assign a positive real coordinate to each element of Fin k. Write m for their arithmetic mean, V for their total squared deviation, and r for the nonnegative radius defined below. The lower and upper nodes are m-r and m+(k-1)r.")),
                Paragraph(Math(Disp(DefinitionsFormula()))),
                Paragraph(Text(
                    "The strict square-sum inequality sum_sq_lt_sq_sum gives ∑ᵢxᵢ² < (∑ᵢxᵢ)². "
                    + "Since V = ∑ᵢxᵢ² - km² and ∑ᵢxᵢ = km, this implies V < k(k-1)m² and r < m. "
                    + "The centered coordinates sum to zero. Cauchy-Schwarz on all indices other than "
                    + "a chosen index bounds its squared deviation by (k-1) times the remaining squared "
                    + "deviations. Substitution of the radius gives the upper bound, including when V is zero."))),
            DescribeRole.Theorem))));

    private static Formula StrictSquareSumFormula()
    {
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        Formula sum = Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, Call("Fin", k)), Sp);
        Formula positive = All("i", Call("Fin", k), Less(D(0), Call("x", i)));
        Formula antecedent = Conjunction(LessEqual(D(2), k), positive);
        Formula sumOfSquares = Seq(sum, Call("x", i), Caret, Grp(D(2)));
        Formula squaredSum = new Formula.Power(Parenthesized(Seq(sum, Call("x", i))), D(2));
        return Disp(All("k", Call("Nat"),
            All("x", Seq(Call("Fin", k), Sp, To, Sp, Call("Real")),
                Implication(antecedent, Less(sumOfSquares, squaredSum)))));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, Parenthesized(body));

    private static Formula DefinitionsFormula()
    {
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula v = F.Id("V");
        Formula sum = Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, Call("Fin", k)), Sp);
        return Seq(
            m, Sp, Eq, Sp, Frac, Grp(sum, Call("x", i)), Grp(k), Comma, Sp,
            v, Sp, Eq, Sp, sum, Open, Call("x", i), Minus, m, Close, Caret, Grp(D(2)), Comma, Sp,
            F.Id("r"), Sp, Eq, Sp, Sqrt, Grp(Frac, Grp(v), Grp(k, Open, k, Minus, D(1), Close)));
    }

    private static Formula TheoremFormula()
    {
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula r = F.Id("r");
        return Disp(Seq(
            Forall, Sp, k, Colon, Sp, Call("Nat"), Comma, Sp,
            Forall, Sp, F.Id("x"), Colon, Sp, Call("Fin", k), Sp, To, Sp, Call("Real"), Comma, Sp,
            Open, D(2), Sp, Le, Sp, k, Sp, Land, Sp,
                Open, Forall, Sp, i, Colon, Sp, Call("Fin", k), Comma, Sp,
                    D(0), Sp, Lt, Sp, Call("x", i), Close, Close,
            Sp, Implies, Sp, Open,
            D(0), Sp, Lt, Sp, m, Minus, r, Sp, Land, Sp,
            Open, Forall, Sp, i, Colon, Sp, Call("Fin", k), Comma, Sp,
                Call("x", i), Sp, Le, Sp, m, Plus, Open, k, Minus, D(1), Close, r, Close, Close));
    }
}
