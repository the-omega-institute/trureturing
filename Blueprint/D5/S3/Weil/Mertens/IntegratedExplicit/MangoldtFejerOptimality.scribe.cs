using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class MangoldtFejerOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The optimal coefficient in the Fejér average",
        H("Cosine moments on a half interval"),
        Blocks(Paragraph(Text(
            "Let μ be a probability measure carried by the interval from zero to one half. "
            + "Write A for the μ-average of b/2 − b² and C(t) for the μ-average of cos(tb).")),
        Describe.Lean(
            DescribeId.Create("integral-gap-eq-sub-tsum"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality.integral_gap_eq_sub_tsum"),
            H("The exact Fourier correction"),
            StatementSource.FromAuthor(Identity()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Evaluate Mathlib's cosine series for the second Bernoulli polynomial at 2b. "
                    + "The absolute values of its terms are bounded by the reciprocal squares, "
                    + "which permits termwise integration against any such μ, including measures with atoms."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("integral-gap-le-and-eq-iff"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality.integral_gap_le_and_eq_iff"),
            H("The bound and its equality condition"),
            StatementSource.FromAuthor(Bound()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "If each cosine moment at frequency 4πn is nonnegative for positive integers n, "
                    + "the correction is a sum of nonnegative terms. It vanishes exactly when every such moment vanishes.")),
                Paragraph(Text(
                    "The differences of two independent uniform points on the half interval give the "
                    + "triangular law and attain 1/24. The arithmetic estimate in MangoldtUniformFejerGap "
                    + "uses half of the average, which gives the coefficient 1/48 for this averaging argument."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("is-greatest-fejer-averaging-coefficient"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality.isGreatest_fejer_averaging_coefficient"),
            H("The attained arithmetic coefficient"),
            StatementSource.FromAuthor(Disp(Equal(F.Id("maximumCoefficient"),
                new Formula.Fraction(D(1), D(4, 8))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Here maximumCoefficient is the greatest value of A/2 among the probability measures "
                + "with C(t) nonnegative for every real t. The density 4 − 8b gives C(0) = 1. For "
                + "nonzero t, integration gives C(t) = 8(1 − cos(t/2))/t² and zero at every "
                + "positive harmonic. The equality condition yields attainment."))),
            DescribeRole.Theorem))));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Moment()
    {
        var frequency = Multiply(Multiply(D(4), Pi), F.Id("n"));
        return new Formula.FunctionCall(FormulaIdentifier.Create("C"), [frequency]);
    }

    private static Formula Identity()
    {
        var correctionTerm = new Formula.Fraction(Moment(), new Formula.Power(F.Id("n"), D(2)));
        var series = Seq(Sum, Underscore, Grp(F.Id("n"), Eq, D(1)), Caret, Grp(Infty), Sp, correctionTerm);
        var correction = new Formula.Fraction(series, Multiply(D(4), new Formula.Power(Pi, D(2))));
        return Disp(Equal(F.Id("A"), Subtract(new Formula.Fraction(D(1), D(2, 4)), correction)));
    }

    private static Formula Bound()
    {
        var a = F.Id("A");
        var value = new Formula.Fraction(D(1), D(2, 4));
        var zeroMoments = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            F.Id("PositiveIntegers"), Equal(Moment(), D(0)));
        var equality = new Formula.Logic(Equal(a, value), FormulaLogicOperator.Iff, zeroMoments);
        return Disp(new Formula.Logic(AtMost(a, value), FormulaLogicOperator.And, equality));
    }
}
