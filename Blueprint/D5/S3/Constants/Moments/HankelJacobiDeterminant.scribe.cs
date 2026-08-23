using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class HankelJacobiDeterminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant-defined Hankel Jacobi coefficient satisfies its squared ratio and "
            + "is positive when three neighboring determinants are positive.",
        H("Hankel Determinant Jacobi Coefficient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hankel-jacobi-coefficient-squared-determinant-ratio"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Moments/HankelJacobiDeterminant."
                        + "hankel_jacobi_coefficient_sq_eq_det_ratio"),
                H("The determinant-defined coefficient obeys the Hankel ratio"),
                StatementSource.FromAuthor(DeterminantRatioFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a real moment sequence m, let the order-j determinant be that of "
                            + "the (j + 1)-square Hankel matrix with entry m(r + s). At every "
                            + "positive index k, a nonnegative product of the two neighboring "
                            + "determinants gives a real square root, while a nonzero current "
                            + "determinant permits division.")),
                    Paragraph(Text(
                        "Under those hypotheses, squaring the determinant-defined coefficient "
                            + "gives the neighboring-determinant product divided by the square "
                            + "of the current determinant. This identifies only the value built "
                            + "from the square root and Hankel determinants; it does not assert "
                            + "that the value is a coefficient of an orthogonal-polynomial "
                            + "recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-hankel-jacobi-coefficient"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Moments/HankelJacobiDeterminant."
                        + "hankel_jacobi_coefficient_pos"),
                H("Positive neighboring determinants give a positive coefficient"),
                StatementSource.FromAuthor(PositiveCoefficientFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If the preceding, current, and following leading Hankel determinants "
                            + "are all positive, then the product under the square root is "
                            + "positive and its square root is positive. Dividing by the positive "
                            + "current determinant leaves the determinant-defined coefficient "
                            + "strictly positive.")),
                    Paragraph(Text(
                        "These hypotheses also satisfy the nonnegativity and nonvanishing "
                            + "conditions of the squared identity. The extra sign information "
                            + "selects the positive value that is lost when only the square of "
                            + "the coefficient is retained."))),
                DescribeRole.Lemma))));

    private static Formula DeterminantRatioFormula()
    {
        Formula moment = F.Id("m");
        Formula index = F.Id("k");
        Formula previous = HankelDet(moment, Previous(index));
        Formula current = HankelDet(moment, index);
        Formula next = HankelDet(moment, Next(index));
        Formula product = Seq(previous, Sp, Times, Sp, next);
        Formula coefficientSquared = Seq(
            HankelJacobiCoefficient(moment, index), Caret, Grp(D(2)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, moment, Colon, Sp,
            Mathbb, Grp(F.Id("N")), Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            index, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, RowBreak, Grp(),
            D(0), Sp, Leq, Sp, product, Sp, Land, Sp,
            current, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp, RowBreak, Grp(),
            coefficientSquared, Sp, Eq, Sp,
            Frac, Grp(product), Grp(current, Caret, Grp(D(2))), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula PositiveCoefficientFormula()
    {
        Formula moment = F.Id("m");
        Formula index = F.Id("k");
        Formula previous = HankelDet(moment, Previous(index));
        Formula current = HankelDet(moment, index);
        Formula next = HankelDet(moment, Next(index));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, moment, Colon, Sp,
            Mathbb, Grp(F.Id("N")), Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            index, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, previous, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, current, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, next, Sp, Rightarrow, Sp, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, HankelJacobiCoefficient(moment, index), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula HankelDet(Formula moment, Formula order) =>
        Call("hankelDet", moment, order);

    private static Formula HankelJacobiCoefficient(Formula moment, Formula index) =>
        Call("hankelJacobiCoefficient", moment, index);

    private static Formula Previous(Formula index) =>
        Seq(index, Sp, Minus, Sp, D(1));

    private static Formula Next(Formula index) =>
        Seq(index, Sp, Plus, Sp, D(1));
}
