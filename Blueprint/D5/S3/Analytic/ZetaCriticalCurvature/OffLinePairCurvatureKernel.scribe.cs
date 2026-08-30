using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCriticalCurvature;

internal sealed class OffLinePairCurvatureKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflection-paired logarithmic potential has a certified slope whose axis derivative is the off-line curvature dipole.",
        H("Off Line Pair Curvature Kernel"),
        Blocks(
            Theorem(
                "radial-quadratic-has-deriv-at",
                "radial_quadratic_hasDerivAt",
                RadialQuadraticHasderivatFormula(),
                "Radial Quadratic Has Deriv At",
                "Derivative of the radial quadratic.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "radial-log-potential-has-deriv-at",
                "radial_log_potential_hasDerivAt",
                RadialLogPotentialHasderivatFormula(),
                "Radial Log Potential Has Deriv At",
                "The displayed slope is the ordinary derivative whenever the local factor is nonzero.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "radial-log-slope-has-deriv-at",
                "radial_log_slope_hasDerivAt",
                RadialLogSlopeHasderivatFormula(),
                "Radial Log Slope Has Deriv At",
                "Derivative of the certified slope field.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "radial-quadratic-axis-pos",
                "radial_quadratic_axis_pos",
                RadialQuadraticAxisPosFormula(),
                "Radial Quadratic Axis pos",
                "Positive displacement keeps both local factors nonzero at the fixed axis.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-potential-has-deriv-at-axis-zero",
                "off_line_pair_potential_hasDerivAt_axis_zero",
                OffLinePairPotentialHasderivatAxisZeroFormula(),
                "Off Line Pair Potential Has Deriv At Axis Zero",
                "The paired potential has zero first normal derivative on the fixed axis.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-slope-has-deriv-at-axis",
                "off_line_pair_slope_hasDerivAt_axis",
                OffLinePairSlopeHasderivatAxisFormula(),
                "Off Line Pair Slope Has Deriv At Axis",
                "The derivative of the certified first-derivative field at the fixed axis is exactly the off-line curvature dipole.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-center",
                "off_line_pair_curvature_center",
                OffLinePairCurvatureCenterFormula(),
                "Off Line Pair Curvature Center",
                "Center value of the dipole.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-right-zero",
                "off_line_pair_curvature_right_zero",
                OffLinePairCurvatureRightZeroFormula(),
                "Off Line Pair Curvature Right Zero",
                "Right zero crossing at tangential offset delta.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-left-zero",
                "off_line_pair_curvature_left_zero",
                OffLinePairCurvatureLeftZeroFormula(),
                "Off Line Pair Curvature Left Zero",
                "Left zero crossing at tangential offset -delta.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-center-neg",
                "off_line_pair_curvature_center_neg",
                OffLinePairCurvatureCenterNegFormula(),
                "Off Line Pair Curvature Center neg",
                "The center of a genuine off-axis pair is a negative curvature well.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-reflection",
                "off_line_pair_curvature_reflection",
                OffLinePairCurvatureReflectionFormula(),
                "Off Line Pair Curvature Reflection",
                "The dipole kernel is even in tangential displacement around its center.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        Formula statement,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

private static Formula RadialQuadraticHasderivatFormula() => Statement(
    [Typed(Seq(F.Id("a")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("y")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("u")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("HasDerivAt"), Sp, Open, F.Id("radialQuadratic"), Sp, F.Id("a"), Sp, F.Id("y"), Close, Sp, Open, D(2), Sp, Times, Sp, Open, F.Id("u"), Sp, Minus, Sp, F.Id("a"), Close, Close, Sp, F.Id("u")));

private static Formula RadialLogPotentialHasderivatFormula() => Statement(
    [Typed(Seq(F.Id("a")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("y")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("u")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("radialQuadratic"), Sp, F.Id("a"), Sp, F.Id("y"), Sp, F.Id("u"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("HasDerivAt"), Sp, Open, F.Id("radialLogPotential"), Sp, F.Id("a"), Sp, F.Id("y"), Close, Sp, Open, F.Id("radialLogSlope"), Sp, F.Id("a"), Sp, F.Id("y"), Sp, F.Id("u"), Close, Sp, F.Id("u")));

private static Formula RadialLogSlopeHasderivatFormula() => Statement(
    [Typed(Seq(F.Id("a")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("y")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("u")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("radialQuadratic"), Sp, F.Id("a"), Sp, F.Id("y"), Sp, F.Id("u"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("HasDerivAt"), Sp, Open, F.Id("radialLogSlope"), Sp, F.Id("a"), Sp, F.Id("y"), Close, Sp, Open, Open, F.Id("y"), Sp, Caret, D(2), Sp, Minus, Sp, Open, F.Id("u"), Sp, Minus, Sp, F.Id("a"), Close, Sp, Caret, D(2), Close, Sp, Slash, Sp, Open, F.Id("radialQuadratic"), Sp, F.Id("a"), Sp, F.Id("y"), Sp, F.Id("u"), Close, Sp, Caret, D(2), Close, Sp, F.Id("u")));

private static Formula RadialQuadraticAxisPosFormula() => Statement(
    [Typed(Seq(F.Id("delta")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("y")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(0), Sp, Lt, Sp, F.Id("delta"))],
        Seq(D(0), Sp, Lt, Sp, F.Id("radialQuadratic"), Sp, F.Id("delta"), Sp, F.Id("y"), Sp, D(0), Sp, Land, Sp, D(0), Sp, Lt, Sp, F.Id("radialQuadratic"), Sp, Open, Minus, F.Id("delta"), Close, Sp, F.Id("y"), Sp, D(0)));

private static Formula OffLinePairPotentialHasderivatAxisZeroFormula() => Statement(
    [Typed(Seq(F.Id("delta")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("gamma")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("t")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(0), Sp, Lt, Sp, F.Id("delta"))],
        Seq(F.Id("HasDerivAt"), Sp, Open, LambdaLower, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, F.Id("offLinePairPotential"), Sp, F.Id("delta"), Sp, F.Id("gamma"), Sp, F.Id("u"), Sp, F.Id("t"), Close, Sp, D(0), Sp, D(0)));

private static Formula OffLinePairSlopeHasderivatAxisFormula() => Statement(
    [Typed(Seq(F.Id("delta")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("gamma")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("t")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(0), Sp, Lt, Sp, F.Id("delta"))],
        Seq(F.Id("HasDerivAt"), Sp, Open, LambdaLower, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, F.Id("offLinePairSlope"), Sp, F.Id("delta"), Sp, F.Id("gamma"), Sp, F.Id("u"), Sp, F.Id("t"), Close, Sp, Open, F.Id("offLinePairCurvatureKernel"), Sp, F.Id("delta"), Sp, F.Id("gamma"), Sp, F.Id("t"), Close, Sp, D(0)));

private static Formula OffLinePairCurvatureCenterFormula() => Statement(
    [Typed(Seq(F.Id("delta")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("gamma")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("delta"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("offLinePairCurvatureKernel"), Sp, F.Id("delta"), Sp, F.Id("gamma"), Sp, F.Id("gamma"), Sp, Eq, Sp, Minus, D(2), Sp, Slash, Sp, F.Id("delta"), Sp, Caret, D(2)));

private static Formula OffLinePairCurvatureRightZeroFormula() => Statement(
    [Typed(Seq(F.Id("delta")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("gamma")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("delta"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("offLinePairCurvatureKernel"), Sp, F.Id("delta"), Sp, F.Id("gamma"), Sp, Open, F.Id("gamma"), Sp, Plus, Sp, F.Id("delta"), Close, Sp, Eq, Sp, D(0)));

private static Formula OffLinePairCurvatureLeftZeroFormula() => Statement(
    [Typed(Seq(F.Id("delta")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("gamma")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("delta"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("offLinePairCurvatureKernel"), Sp, F.Id("delta"), Sp, F.Id("gamma"), Sp, Open, F.Id("gamma"), Sp, Minus, Sp, F.Id("delta"), Close, Sp, Eq, Sp, D(0)));

private static Formula OffLinePairCurvatureCenterNegFormula() => Statement(
    [Typed(Seq(F.Id("delta")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("gamma")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(0), Sp, Lt, Sp, F.Id("delta"))],
        Seq(F.Id("offLinePairCurvatureKernel"), Sp, F.Id("delta"), Sp, F.Id("gamma"), Sp, F.Id("gamma"), Sp, Lt, Sp, D(0)));

private static Formula OffLinePairCurvatureReflectionFormula() => Statement(
    [Typed(Seq(F.Id("delta")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("gamma")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("y")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("offLinePairCurvatureKernel"), Sp, F.Id("delta"), Sp, F.Id("gamma"), Sp, Open, F.Id("gamma"), Sp, Minus, Sp, F.Id("y"), Close, Sp, Eq, Sp, F.Id("offLinePairCurvatureKernel"), Sp, F.Id("delta"), Sp, F.Id("gamma"), Sp, Open, F.Id("gamma"), Sp, Plus, Sp, F.Id("y"), Close));

private static Formula Typed(Formula name, Formula type) =>
    Seq(name, Colon, Sp, type);

private static Formula Statement(
    Formula[] binders,
    Formula[] constraints,
    Formula[] hypotheses,
    Formula conclusion)
{
    List<Formula> items = [];
    if (binders.Length > 0)
    {
        items.Add(Forall);
        items.Add(Sp);
    }
    for (int index = 0; index < binders.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(binders[index]);
    }
    foreach (Formula constraint in constraints)
    {
        if (binders.Length > 0 || constraint != constraints[0])
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(constraint);
    }
    if (binders.Length > 0 || constraints.Length > 0)
    {
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    for (int index = 0; index < hypotheses.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Sp);
            items.Add(Land);
            items.Add(Sp);
        }
        items.Add(Seq(Open, hypotheses[index], Close));
    }
    if (hypotheses.Length > 0)
    {
        items.Add(Sp);
        items.Add(Rightarrow);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    items.Add(Seq(Open, conclusion, Close));
    items.Add(Dot);
    return Disp(Seq([.. items]));
}
}
