using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenScaleHelixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden completion lifts to a helix whose deck step advances one scale period and reverses orientation.",
        H("Golden Scale Helix"),
        Blocks(
            Theorem(
                "golden-scale-period-pos",
                "golden_scale_period_pos",
                GoldenScalePeriodPosFormula(),
                "Golden Scale Period pos",
                "The golden logarithmic scale period is strictly positive.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-scale-period-eq-neg-log-multiplier",
                "golden_scale_period_eq_neg_log_multiplier",
                GoldenScalePeriodEqNegLogMultiplierFormula(),
                "Golden Scale Period eq neg Log Multiplier",
                "The logarithmic scale period is exactly the negative logarithm of the absolute golden projective multiplier.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-level",
                "goldenHelixStep_level",
                GoldenhelixstepLevelFormula(),
                "Golden Helix Step Level",
                "This theorem establishes golden helix step level in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-scale-lift",
                "goldenHelixStep_scaleLift",
                GoldenhelixstepScaleliftFormula(),
                "Golden Helix Step Scale Lift",
                "This theorem establishes golden helix step scale lift in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-orientation",
                "goldenHelixStep_orientation",
                GoldenhelixstepOrientationFormula(),
                "Golden Helix Step Orientation",
                "This theorem establishes golden helix step orientation in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-twice-orientation",
                "goldenHelixStep_twice_orientation",
                GoldenhelixstepTwiceOrientationFormula(),
                "Golden Helix Step Twice Orientation",
                "Two completion turns restore the orientation sheet.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-twice-scale-lift",
                "goldenHelixStep_twice_scaleLift",
                GoldenhelixstepTwiceScaleliftFormula(),
                "Golden Helix Step Twice Scale Lift",
                "Two completion turns add exactly two golden scale periods.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-scale-lift-strict",
                "goldenHelixStep_scaleLift_strict",
                GoldenhelixstepScaleliftStrictFormula(),
                "Golden Helix Step Scale Lift Strict",
                "Every completion turn strictly increases the lifted scale coordinate.",
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

private static Formula GoldenScalePeriodPosFormula() => Statement(
    [],
        [],
        [],
        Seq(D(0), Sp, Lt, Sp, F.Id("goldenScalePeriod")));

private static Formula GoldenScalePeriodEqNegLogMultiplierFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("goldenScalePeriod"), Sp, Eq, Sp, Minus, F.Id("Real"), Dot, F.Id("log"), Sp, Bar, F.Id("goldenProjectiveMultiplier"), Bar));

private static Formula GoldenhelixstepLevelFormula() => Statement(
    [Typed(Seq(F.Id("state")), Seq(F.Id("GoldenHelixState")))],
        [],
        [],
        Seq(Open, F.Id("goldenHelixStep"), Sp, F.Id("state"), Close, Dot, F.Id("level"), Sp, Eq, Sp, F.Id("state"), Dot, F.Id("level"), Sp, Plus, Sp, D(1)));

private static Formula GoldenhelixstepScaleliftFormula() => Statement(
    [Typed(Seq(F.Id("state")), Seq(F.Id("GoldenHelixState")))],
        [],
        [],
        Seq(Open, F.Id("goldenHelixStep"), Sp, F.Id("state"), Close, Dot, F.Id("scaleLift"), Sp, Eq, Sp, F.Id("state"), Dot, F.Id("scaleLift"), Sp, Plus, Sp, F.Id("goldenScalePeriod")));

private static Formula GoldenhelixstepOrientationFormula() => Statement(
    [Typed(Seq(F.Id("state")), Seq(F.Id("GoldenHelixState")))],
        [],
        [],
        Seq(Open, F.Id("goldenHelixStep"), Sp, F.Id("state"), Close, Dot, F.Id("orientation"), Sp, Eq, Sp, Bang, F.Id("state"), Dot, F.Id("orientation")));

private static Formula GoldenhelixstepTwiceOrientationFormula() => Statement(
    [Typed(Seq(F.Id("state")), Seq(F.Id("GoldenHelixState")))],
        [],
        [],
        Seq(Open, F.Id("goldenHelixStep"), Sp, Open, F.Id("goldenHelixStep"), Sp, F.Id("state"), Close, Close, Dot, F.Id("orientation"), Sp, Eq, Sp, F.Id("state"), Dot, F.Id("orientation")));

private static Formula GoldenhelixstepTwiceScaleliftFormula() => Statement(
    [Typed(Seq(F.Id("state")), Seq(F.Id("GoldenHelixState")))],
        [],
        [],
        Seq(Open, F.Id("goldenHelixStep"), Sp, Open, F.Id("goldenHelixStep"), Sp, F.Id("state"), Close, Close, Dot, F.Id("scaleLift"), Sp, Eq, Sp, F.Id("state"), Dot, F.Id("scaleLift"), Sp, Plus, Sp, D(2), Sp, Times, Sp, F.Id("goldenScalePeriod")));

private static Formula GoldenhelixstepScaleliftStrictFormula() => Statement(
    [Typed(Seq(F.Id("state")), Seq(F.Id("GoldenHelixState")))],
        [],
        [],
        Seq(F.Id("state"), Dot, F.Id("scaleLift"), Sp, Lt, Sp, Open, F.Id("goldenHelixStep"), Sp, F.Id("state"), Close, Dot, F.Id("scaleLift")));

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
