using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenMobiusMapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal golden Mobius map has the golden ratio and its conjugate as fixed points and preserves the positive half-line.",
        H("Golden Mobius Map"),
        Blocks(
            Theorem(
                "golden-mobius-fixed-golden",
                "golden_mobius_fixed_golden",
                GoldenMobiusFixedGoldenFormula(),
                "Golden Mobius Fixed Golden",
                "The positive golden root is a fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-fixed-conjugate",
                "golden_mobius_fixed_conjugate",
                GoldenMobiusFixedConjugateFormula(),
                "Golden Mobius Fixed Conjugate",
                "The negative conjugate golden root is the second fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-fixed-points-ne",
                "golden_fixed_points_ne",
                GoldenFixedPointsNeFormula(),
                "Golden Fixed Points ne",
                "The two fixed points are distinct.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-fixed-point-gap",
                "golden_fixed_point_gap",
                GoldenFixedPointGapFormula(),
                "Golden Fixed Point Gap",
                "Their oriented gap is the square root of the discriminant.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-pos",
                "golden_mobius_pos",
                GoldenMobiusPosFormula(),
                "Golden Mobius pos",
                "Positive starting points remain in the positive affine chart.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-multiplier-eq-neg-conjugate-sq",
                "golden_projective_multiplier_eq_neg_conjugate_sq",
                GoldenProjectiveMultiplierEqNegConjugateSqFormula(),
                "Golden Projective Multiplier eq neg Conjugate Sq",
                "The projective multiplier can equivalently be read from the stable golden conjugate eigenvalue.",
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

private static Formula GoldenMobiusFixedGoldenFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("goldenMobius"), Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("goldenRatio")));

private static Formula GoldenMobiusFixedConjugateFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("goldenMobius"), Sp, F.Id("Real"), Dot, F.Id("goldenConj"), Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("goldenConj")));

private static Formula GoldenFixedPointsNeFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Neq, Sp, F.Id("Real"), Dot, F.Id("goldenConj")));

private static Formula GoldenFixedPointGapFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Minus, Sp, F.Id("Real"), Dot, F.Id("goldenConj"), Sp, Eq, Sp, F.Id("Real"), Dot, F.Id("sqrt"), Sp, D(5)));

private static Formula GoldenMobiusPosFormula() => Statement(
    [Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(D(0), Sp, Lt, Sp, F.Id("x"))],
        Seq(D(0), Sp, Lt, Sp, F.Id("goldenMobius"), Sp, F.Id("x")));

private static Formula GoldenProjectiveMultiplierEqNegConjugateSqFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("goldenProjectiveMultiplier"), Sp, Eq, Sp, Minus, Open, F.Id("Real"), Dot, F.Id("goldenConj"), Sp, Caret, D(2), Close));

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
