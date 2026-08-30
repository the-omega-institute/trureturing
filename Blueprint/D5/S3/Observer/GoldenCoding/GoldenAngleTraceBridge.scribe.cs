using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenAngleTraceBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rotation trace sends thirty-six degrees to the golden ratio.",
        H("Golden Angle Trace Bridge"),
        Blocks(
            Theorem(
                "thirty-six-degrees-eq-golden-angle",
                "thirty_six_degrees_eq_golden_angle",
                ThirtySixDegreesEqGoldenAngleFormula(),
                "Thirty Six Degrees eq Golden Angle",
                "Thirty-six degrees is exactly the golden angle in radians.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-angle-trace-eq-golden-ratio",
                "golden_angle_trace_eq_golden_ratio",
                GoldenAngleTraceEqGoldenRatioFormula(),
                "Golden Angle Trace eq Golden Ratio",
                "The trace of the thirty-six-degree rotation is exactly the golden ratio.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "thirty-six-degree-trace-eq-golden-ratio",
                "thirty_six_degree_trace_eq_golden_ratio",
                ThirtySixDegreeTraceEqGoldenRatioFormula(),
                "Thirty Six Degree Trace eq Golden Ratio",
                "Degree-valued formulation of the golden trace identity.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "rotation-trace-neg",
                "rotation_trace_neg",
                RotationTraceNegFormula(),
                "Rotation Trace neg",
                "The trace observer forgets orientation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-angle-ne-neg",
                "golden_angle_ne_neg",
                GoldenAngleNeNegFormula(),
                "Golden Angle ne neg",
                "The golden angle is genuinely distinct from its reflected angle.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "rotation-trace-not-injective",
                "rotation_trace_not_injective",
                RotationTraceNotInjectiveFormula(),
                "Rotation Trace Not Injective",
                "Consequently the trace observer is not injective.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-angle-trace-quadratic",
                "golden_angle_trace_quadratic",
                GoldenAngleTraceQuadraticFormula(),
                "Golden Angle Trace Quadratic",
                "The observed trace retains the golden quadratic relation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-angle-trace-reciprocal-fixed",
                "golden_angle_trace_reciprocal_fixed",
                GoldenAngleTraceReciprocalFixedFormula(),
                "Golden Angle Trace Reciprocal Fixed",
                "The trace also retains the reciprocal fixed-point presentation.",
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

private static Formula ThirtySixDegreesEqGoldenAngleFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("degreesToRadians"), Sp, D(3, 6), Sp, Eq, Sp, F.Id("goldenAngle")));

private static Formula GoldenAngleTraceEqGoldenRatioFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("rotationTrace"), Sp, F.Id("goldenAngle"), Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("goldenRatio")));

private static Formula ThirtySixDegreeTraceEqGoldenRatioFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("rotationTrace"), Sp, Open, F.Id("degreesToRadians"), Sp, D(3, 6), Close, Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("goldenRatio")));

private static Formula RotationTraceNegFormula() => Statement(
    [Typed(Seq(F.Id("theta")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("rotationTrace"), Sp, Open, Minus, F.Id("theta"), Close, Sp, Eq, Sp, F.Id("rotationTrace"), Sp, F.Id("theta")));

private static Formula GoldenAngleNeNegFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("goldenAngle"), Sp, Neq, Sp, Minus, F.Id("goldenAngle")));

private static Formula RotationTraceNotInjectiveFormula() => Statement(
    [],
        [],
        [],
        Seq(Neg, Sp, F.Id("Function"), Dot, F.Id("Injective"), Sp, F.Id("rotationTrace")));

private static Formula GoldenAngleTraceQuadraticFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("rotationTrace"), Sp, F.Id("goldenAngle"), Sp, Caret, D(2), Sp, Eq, Sp, F.Id("rotationTrace"), Sp, F.Id("goldenAngle"), Sp, Plus, Sp, D(1)));

private static Formula GoldenAngleTraceReciprocalFixedFormula() => Statement(
    [],
        [],
        [],
        Seq(D(1), Sp, Plus, Sp, D(1), Sp, Slash, Sp, F.Id("rotationTrace"), Sp, F.Id("goldenAngle"), Sp, Eq, Sp, F.Id("rotationTrace"), Sp, F.Id("goldenAngle")));

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
