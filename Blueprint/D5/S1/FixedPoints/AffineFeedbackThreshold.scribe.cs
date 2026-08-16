using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class AffineFeedbackThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An affine feedback map contracts below unit gain, expands above it, and is critical at one.",
        H("Affine Feedback Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("affine-feedback-has-a-unit-gain-threshold"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/AffineFeedbackThreshold.affine_feedback_threshold"),
                H("Affine feedback has a unit-gain threshold"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f(x) = a + bx on the active affine region and let "
                            + "x* = a/(1-b) away from unit gain. If b is nonnegative and "
                            + "strictly below one, f is a contraction, x* is its unique fixed "
                            + "point, and every affine iterate converges to x*.")),
                    Paragraph(Text(
                        "If b is greater than one, x* remains fixed and every nonzero "
                            + "deviation from it is multiplied in distance by b, hence strictly "
                            + "amplified. At b = 1, the map preserves every pairwise distance.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle supplied the exact contraction declarations "
                            + "ContractingWith.fixedPoint_unique and "
                            + "ContractingWith.tendsto_iterate_fixedPoint, both applied by the "
                            + "module. Local and repository searches found no declaration "
                            + "packaging all three gain regimes; LeanSearch returned HTTP 404."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Dist(Formula left, Formula right) =>
        Seq(Operatorname, Grp(F.Id("dist")), Open, left, Comma, Sp, right, Close);

    private static Formula ThresholdFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula f = F.Id("f");
        Formula xStar = Seq(x, Caret, Grp(Star));
        Formula fx = Apply(f, x);
        Formula fy = Apply(f, y);
        Formula fStar = Apply(f, xStar);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, a, Comma, Sp, b, InMacro, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
            f, Open, x, Close, Eq, a, Plus, b, x, Comma, Sp,
            xStar, Eq, Frac, Grp(a), Grp(D(1), Minus, b), Comma, RowBreak,
            Open, D(0), Leq, Sp, b, Lt, D(1), Rightarrow, Sp,
            Operatorname, Grp(F.Id("Contracting")), Open, f, Comma, b, Close, Land, Sp,
            Open, Forall, Sp, x, Comma, Sp,
            Open, fx, Eq, x, Leftrightarrow, Sp, x, Eq, xStar, Close, Land, Sp,
            Apply(Seq(f, Caret, Grp(F.Id("n"))), x), To, Sp, xStar, Close, Close,
            Comma, RowBreak,
            Open, D(1), Lt, b, Rightarrow, Sp, fStar, Eq, xStar, Land, Sp,
            Open, Forall, Sp, x, Neq, Sp, xStar, Comma, Sp,
            Dist(fx, xStar), Eq, b, Dist(x, xStar), Gt, Dist(x, xStar), Close, Close,
            Comma, RowBreak,
            Open, b, Eq, D(1), Rightarrow, Sp, Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            Dist(fx, fy), Eq, Dist(x, y), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
