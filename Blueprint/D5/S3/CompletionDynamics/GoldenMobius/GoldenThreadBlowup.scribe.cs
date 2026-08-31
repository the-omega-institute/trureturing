using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenThreadBlowupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden completion curves share the same completed value while their first blow-up coordinate and tangent retain the observer origin.",
        H("Golden Thread Blowup"),
        Blocks(
            Theorem(
                "golden-thread-curve-zero",
                "golden_thread_curve_zero",
                GoldenThreadCurveZeroFormula(),
                "Golden Thread Curve Zero",
                "This theorem establishes golden thread curve zero in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-curve-sub-golden",
                "golden_thread_curve_sub_golden",
                GoldenThreadCurveSubGoldenFormula(),
                "Golden Thread Curve Sub Golden",
                "Difference from the completed fixed point in the inverse projective chart.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-curve-sub-conjugate",
                "golden_thread_curve_sub_conjugate",
                GoldenThreadCurveSubConjugateFormula(),
                "Golden Thread Curve Sub Conjugate",
                "Difference from the conjugate fixed point in the inverse projective chart.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-cross-ratio-thread-curve",
                "golden_cross_ratio_thread_curve",
                GoldenCrossRatioThreadCurveFormula(),
                "Golden Cross Ratio Thread Curve",
                "The inverse chart recovers the prescribed projective coordinate exactly.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-curve-has-deriv-at",
                "golden_thread_curve_hasDerivAt",
                GoldenThreadCurveHasderivatFormula(),
                "Golden Thread Curve Has Deriv At",
                "The inverse golden chart has first derivative c(φ-ψ) at completion.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-curve-has-deriv-at-sqrt-five",
                "golden_thread_curve_hasDerivAt_sqrt_five",
                GoldenThreadCurveHasderivatSqrtFiveFormula(),
                "Golden Thread Curve Has Deriv At Sqrt Five",
                "The tangent coefficient displays the discriminant gap sqrt 5.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-completion-value-eq",
                "golden_thread_completion_value_eq",
                GoldenThreadCompletionValueEqFormula(),
                "Golden Thread Completion Value eq",
                "Two origin coefficients give the same completed value.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-tangent-injective",
                "golden_thread_tangent_injective",
                GoldenThreadTangentInjectiveFormula(),
                "Golden Thread Tangent Injective",
                "Distinct origin coefficients give distinct completion tangents.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-geometric-thread-cross-ratio",
                "golden_geometric_thread_cross_ratio",
                GoldenGeometricThreadCrossRatioFormula(),
                "Golden Geometric Thread Cross Ratio",
                "At any depth where the inverse affine chart is defined, the blow-up coordinate is exactly c * multiplier^n.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-geometric-thread-origin-recovery",
                "golden_geometric_thread_origin_recovery",
                GoldenGeometricThreadOriginRecoveryFormula(),
                "Golden Geometric Thread Origin Recovery",
                "Since the multiplier is nonzero, renormalization recovers the origin coefficient at every finite depth.",
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

private static Formula GoldenThreadCurveZeroFormula() => Statement(
    [Typed(Seq(F.Id("c")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("goldenThreadCurve"), Sp, F.Id("c"), Sp, D(0), Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("goldenRatio")));

private static Formula GoldenThreadCurveSubGoldenFormula() => Statement(
    [Typed(Seq(F.Id("c")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(1), Sp, Minus, Sp, F.Id("h"), Sp, Times, Sp, F.Id("c"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("goldenThreadCurve"), Sp, F.Id("c"), Sp, F.Id("h"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Eq, Sp, Open, F.Id("h"), Sp, Times, Sp, F.Id("c"), Close, Sp, Times, Sp, Open, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenConj"), Close, Sp, Slash, Sp, Open, D(1), Sp, Minus, Sp, F.Id("h"), Sp, Times, Sp, F.Id("c"), Close));

private static Formula GoldenThreadCurveSubConjugateFormula() => Statement(
    [Typed(Seq(F.Id("c")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(1), Sp, Minus, Sp, F.Id("h"), Sp, Times, Sp, F.Id("c"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("goldenThreadCurve"), Sp, F.Id("c"), Sp, F.Id("h"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenConj"), Sp, Eq, Sp, Open, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenConj"), Close, Sp, Slash, Sp, Open, D(1), Sp, Minus, Sp, F.Id("h"), Sp, Times, Sp, F.Id("c"), Close));

private static Formula GoldenCrossRatioThreadCurveFormula() => Statement(
    [Typed(Seq(F.Id("c")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("h")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(1), Sp, Minus, Sp, F.Id("h"), Sp, Times, Sp, F.Id("c"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("goldenCrossRatio"), Sp, Open, F.Id("goldenThreadCurve"), Sp, F.Id("c"), Sp, F.Id("h"), Close, Sp, Eq, Sp, F.Id("h"), Sp, Times, Sp, F.Id("c")));

private static Formula GoldenThreadCurveHasderivatFormula() => Statement(
    [Typed(Seq(F.Id("c")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("HasDerivAt"), Sp, Open, F.Id("goldenThreadCurve"), Sp, F.Id("c"), Close, Sp, Open, F.Id("c"), Sp, Times, Sp, Open, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenConj"), Close, Close, Sp, D(0)));

private static Formula GoldenThreadCurveHasderivatSqrtFiveFormula() => Statement(
    [Typed(Seq(F.Id("c")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("HasDerivAt"), Sp, Open, F.Id("goldenThreadCurve"), Sp, F.Id("c"), Close, Sp, Open, F.Id("c"), Sp, Times, Sp, F.Id("Real"), Dot, F.Id("sqrt"), Sp, D(5), Close, Sp, D(0)));

private static Formula GoldenThreadCompletionValueEqFormula() => Statement(
    [Typed(Seq(F.Id("c"), Underscore, Grp(D(1))), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("c"), Underscore, Grp(D(2))), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [],
        Seq(F.Id("goldenThreadCurve"), Sp, F.Id("c"), Underscore, Grp(D(1)), Sp, D(0), Sp, Eq, Sp, F.Id("goldenThreadCurve"), Sp, F.Id("c"), Underscore, Grp(D(2)), Sp, D(0)));

private static Formula GoldenThreadTangentInjectiveFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Function"), Dot, F.Id("Injective"), Sp, Open, LambdaLower, Sp, F.Id("c"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, F.Id("c"), Sp, Times, Sp, F.Id("Real"), Dot, F.Id("sqrt"), Sp, D(5), Close));

private static Formula GoldenGeometricThreadCrossRatioFormula() => Statement(
    [Typed(Seq(F.Id("c")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("n")), Seq(Mathbb, Grp(F.Id("N"))))],
        [],
        [Seq(D(1), Sp, Minus, Sp, F.Id("goldenProjectiveMultiplier"), Sp, Caret, Grp(F.Id("n")), Sp, Times, Sp, F.Id("c"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("goldenCrossRatio"), Sp, Open, F.Id("goldenGeometricThread"), Sp, F.Id("c"), Sp, F.Id("n"), Close, Sp, Eq, Sp, F.Id("goldenProjectiveMultiplier"), Sp, Caret, Grp(F.Id("n")), Sp, Times, Sp, F.Id("c")));

private static Formula GoldenGeometricThreadOriginRecoveryFormula() => Statement(
    [Typed(Seq(F.Id("c")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("n")), Seq(Mathbb, Grp(F.Id("N"))))],
        [],
        [Seq(D(1), Sp, Minus, Sp, F.Id("goldenProjectiveMultiplier"), Sp, Caret, Grp(F.Id("n")), Sp, Times, Sp, F.Id("c"), Sp, Neq, Sp, D(0))],
        Seq(Open, F.Id("goldenProjectiveMultiplier"), Caret, Grp(Minus, D(1)), Close, Sp, Caret, Grp(F.Id("n")), Sp, Times, Sp, F.Id("goldenCrossRatio"), Sp, Open, F.Id("goldenGeometricThread"), Sp, F.Id("c"), Sp, F.Id("n"), Close, Sp, Eq, Sp, F.Id("c")));

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
