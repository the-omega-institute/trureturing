using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class BodeWidthCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var indexType = F.Id("I");
        var index = F.Id("i");
        var y = F.Id("y");
        var tau = F.Id("tau");
        var delta = F.Id("delta");
        var half = new Formula.Fraction(D(1), D(2));
        var deltaAt = Call("delta", index);
        var width = F.Id("W");
        var area = F.Id("A");
        var displacement = F.Id("S");
        var damping = F.Id("R");
        var critical = F.Id("C");
        var widthAt = Call("W", y);

        Formula sumOverIndex(Formula term) =>
            Seq(Sum, Underscore, Grp(index, InMacro, Sp, indexType), term);

        var pulse = MaxOf(Seq(deltaAt, Minus, new Formula.Absolute(Seq(y, Minus, half))), D(0));
        var widthDefinition = sumOverIndex(pulse);
        var areaDefinition = Seq(
            Int, Underscore, Grp(D(0)), Caret, Grp(Infty), widthAt, Thin, F.Id("dy"));
        var positiveWidthZero = Seq(
            Forall, Sp, y, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            y, Gt, D(0), Sp, Rightarrow, Sp, widthAt, Eq, D(0));
        var criticalDefinition = Seq(
            Forall, Sp, index, InMacro, Sp, indexType, Comma, Sp,
            half, Plus, deltaAt, Eq, half, Sp, Land, Sp,
            half, Minus, deltaAt, Eq, half);
        var rightDisplacement = new Formula.Power(
            Seq(Grp(half, Plus, deltaAt, Minus, half)), D(2));
        var leftDisplacement = new Formula.Power(
            Seq(Grp(half, Minus, deltaAt, Minus, half)), D(2));
        var displacementDefinition = sumOverIndex(
            Grp(rightDisplacement, Plus, leftDisplacement));
        var dampingDefinition = sumOverIndex(Seq(
            D(2), Sp, Cdot, Sp,
            Grp(Call("cosh", Seq(tau, Sp, Cdot, Sp, deltaAt)), Minus, D(1))));
        var secondDerivativeAtZero = Call("deriv", Call("deriv", damping), D(0));

        var conclusion = Seq(
            Grp(critical, Sp, Leftrightarrow, Sp, positiveWidthZero), Sp, Land, Sp,
            Grp(positiveWidthZero, Sp, Leftrightarrow, Sp, area, Eq, D(0)), Sp, Land, Sp,
            Grp(area, Eq, half, Sp, Cdot, Sp, displacement), Sp, Land, Sp,
            Grp(area, Eq, half, Sp, Cdot, Sp, secondDerivativeAtZero));

        var statement = Seq(
            Forall, Sp, indexType, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call("Fintype", indexType), Comma, Sp,
            delta, Colon, Sp, indexType, To, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
            Grp(), Grp(
                Seq(Forall, Sp, index, InMacro, Sp, indexType, Comma, Sp,
                    D(0), Leq, deltaAt, Sp, Land, Sp, deltaAt, Leq, half),
                Sp, Rightarrow, Sp, RowBreak, Grp(),
                Operatorname, Grp(F.Id("let")), Sp, critical, Colon, Eq, criticalDefinition,
                Comma, RowBreak, Grp(),
                Operatorname, Grp(F.Id("let")), Sp, width, Open, y, Close, Colon, Eq,
                widthDefinition, Comma, RowBreak, Grp(),
                Operatorname, Grp(F.Id("let")), Sp, area, Colon, Eq, areaDefinition,
                Comma, RowBreak, Grp(),
                Operatorname, Grp(F.Id("let")), Sp, displacement, Colon, Eq,
                displacementDefinition, Comma, RowBreak, Grp(),
                Operatorname, Grp(F.Id("let")), Sp, damping, Open, tau, Close, Colon, Eq,
                dampingDefinition, Comma, RowBreak, Grp(), conclusion));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite mirror-paired widths produce the same critical-line, area, and curvature defect.",
            H("Bode-Width Criterion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("bode-width-criterion"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/Scattering/BodeWidthCriterion.bode_width_criterion"),
                    H("Finite width, displacement, and damping defects coincide"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The source finite window is encoded by nonnegative mirror-pair widths "
                            + "delta bounded by one half. Each pair contributes the displayed "
                            + "triangular pulse. Its integral is delta squared, while the two "
                            + "mirrored real-part displacements contribute twice delta squared. "
                            + "Twice differentiating the finite cosh partition gives the same sum."))),
                    DescribeRole.Theorem)),
            []));
    }

    private static Formula MaxOf(Formula left, Formula right) =>
        Seq(Max, Open, left, Comma, Sp, right, Close);
}
