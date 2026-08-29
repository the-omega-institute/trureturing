using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenCrossRatioLinearizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden cross-ratio coordinates exactly linearize the Mobius map.",
        H("Golden Cross Ratio Linearization"),
        Blocks(
            Theorem(
                "golden-cross-ratio-at-golden",
                "golden_cross_ratio_at_golden",
                GoldenCrossRatioAtGoldenFormula(),
                "Golden Cross Ratio At Golden",
                "This theorem establishes golden cross ratio at golden in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-sub-golden",
                "golden_mobius_sub_golden",
                GoldenMobiusSubGoldenFormula(),
                "Golden Mobius Sub Golden",
                "Numerator identity in a denominator-separated form.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-sub-conjugate",
                "golden_mobius_sub_conjugate",
                GoldenMobiusSubConjugateFormula(),
                "Golden Mobius Sub Conjugate",
                "Denominator identity in a denominator-separated form.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-cross-ratio-linearization",
                "golden_cross_ratio_linearization",
                GoldenCrossRatioLinearizationFormula(),
                "Golden Cross Ratio Linearization",
                "Exact golden projective linearization.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "positive-avoids-golden-singularities",
                "positive_avoids_golden_singularities",
                PositiveAvoidsGoldenSingularitiesFormula(),
                "Positive Avoids Golden Singularities",
                "Positive points avoid both affine-chart singularities.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-iterate-pos",
                "golden_mobius_iterate_pos",
                GoldenMobiusIteratePosFormula(),
                "Golden Mobius Iterate pos",
                "Positivity is invariant under every finite Mobius iterate.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-cross-ratio-iterate",
                "golden_cross_ratio_iterate",
                GoldenCrossRatioIterateFormula(),
                "Golden Cross Ratio Iterate",
                "Exact geometric contraction law on the positive affine chart.",
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

private static Formula GoldenCrossRatioAtGoldenFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("goldenCrossRatio"), Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Eq, Sp, D(0)));

private static Formula GoldenMobiusSubGoldenFormula() => Statement(
    [Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("x"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("goldenMobius"), Sp, F.Id("x"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Eq, Sp, Minus, Open, F.Id("x"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Close, Sp, Slash, Sp, Open, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Times, Sp, F.Id("x"), Close));

private static Formula GoldenMobiusSubConjugateFormula() => Statement(
    [Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("x"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("goldenMobius"), Sp, F.Id("x"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenConj"), Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Times, Sp, Open, F.Id("x"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenConj"), Close, Sp, Slash, Sp, F.Id("x")));

private static Formula GoldenCrossRatioLinearizationFormula() => Statement(
    [Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("x"), Sp, Neq, Sp, D(0)), Seq(F.Id("x"), Sp, Neq, Sp, F.Id("Real"), Dot, F.Id("goldenConj"))],
        Seq(F.Id("goldenCrossRatio"), Sp, Open, F.Id("goldenMobius"), Sp, F.Id("x"), Close, Sp, Eq, Sp, F.Id("goldenProjectiveMultiplier"), Sp, Times, Sp, F.Id("goldenCrossRatio"), Sp, F.Id("x")));

private static Formula PositiveAvoidsGoldenSingularitiesFormula() => Statement(
    [Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(0), Sp, Lt, Sp, F.Id("x"))],
        Seq(F.Id("x"), Sp, Neq, Sp, D(0), Sp, Land, Sp, F.Id("x"), Sp, Neq, Sp, F.Id("Real"), Dot, F.Id("goldenConj")));

private static Formula GoldenMobiusIteratePosFormula() => Statement(
    [Typed(Seq(F.Id("n")), Seq(Mathbb, Grp(F.Id("N")))), Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(0), Sp, Lt, Sp, F.Id("x"))],
        Seq(D(0), Sp, Lt, Sp, Open, F.Id("goldenMobius"), Caret, Grp(OpenBracket, F.Id("n"), CloseBracket), Close, Sp, F.Id("x")));

private static Formula GoldenCrossRatioIterateFormula() => Statement(
    [Typed(Seq(F.Id("n")), Seq(Mathbb, Grp(F.Id("N")))), Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(0), Sp, Lt, Sp, F.Id("x"))],
        Seq(F.Id("goldenCrossRatio"), Sp, Open, Open, F.Id("goldenMobius"), Caret, Grp(OpenBracket, F.Id("n"), CloseBracket), Close, Sp, F.Id("x"), Close, Sp, Eq, Sp, F.Id("goldenProjectiveMultiplier"), Sp, Caret, Grp(F.Id("n")), Sp, Times, Sp, F.Id("goldenCrossRatio"), Sp, F.Id("x")));

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
