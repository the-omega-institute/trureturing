using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenProjectiveDerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden Mobius derivative equals its projective multiplier.",
        H("Golden Projective Derivative"),
        Blocks(
            Theorem(
                "golden-mobius-has-deriv-at",
                "golden_mobius_hasDerivAt",
                GoldenMobiusHasderivatFormula(),
                "Golden Mobius Has Deriv At",
                "Ordinary differentiation gives the same multiplier as exact projective linearization.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "deriv-golden-mobius-at-golden",
                "deriv_golden_mobius_at_golden",
                DerivGoldenMobiusAtGoldenFormula(),
                "Deriv Golden Mobius At Golden",
                "Evaluation of deriv at the golden fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "abs-golden-projective-multiplier",
                "abs_golden_projective_multiplier",
                AbsGoldenProjectiveMultiplierFormula(),
                "Abs Golden Projective Multiplier",
                "The projective multiplier has the expected positive magnitude.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "abs-golden-projective-multiplier-lt-one",
                "abs_golden_projective_multiplier_lt_one",
                AbsGoldenProjectiveMultiplierLtOneFormula(),
                "Abs Golden Projective Multiplier lt One",
                "The completion derivative is a strict contraction in projective coordinates.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "linearized-golden-has-deriv-at-zero",
                "linearized_golden_hasDerivAt_zero",
                LinearizedGoldenHasderivatZeroFormula(),
                "Linearized Golden Has Deriv At Zero",
                "Multiplication by the golden multiplier has that derivative at zero.",
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

private static Formula GoldenMobiusHasderivatFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("HasDerivAt"), Sp, F.Id("goldenMobius"), Sp, F.Id("goldenProjectiveMultiplier"), Sp, F.Id("Real"), Dot, F.Id("goldenRatio")));

private static Formula DerivGoldenMobiusAtGoldenFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("deriv"), Sp, F.Id("goldenMobius"), Sp, F.Id("Real"), Dot, F.Id("goldenRatio"), Sp, Eq, Sp, F.Id("goldenProjectiveMultiplier")));

private static Formula AbsGoldenProjectiveMultiplierFormula() => Statement(
    [],
        [],
        [],
        Seq(Bar, F.Id("goldenProjectiveMultiplier"), Bar, Sp, Eq, Sp, Open, F.Id("Real"), Dot, F.Id("goldenRatio"), Caret, Grp(Minus, D(1)), Close, Sp, Caret, D(2)));

private static Formula AbsGoldenProjectiveMultiplierLtOneFormula() => Statement(
    [],
        [],
        [],
        Seq(Bar, F.Id("goldenProjectiveMultiplier"), Bar, Sp, Lt, Sp, D(1)));

private static Formula LinearizedGoldenHasderivatZeroFormula() => Statement(
    [],
        [],
        [],
        Seq(F.Id("HasDerivAt"), Sp, Open, LambdaLower, Sp, F.Id("y"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, F.Id("goldenProjectiveMultiplier"), Sp, Times, Sp, F.Id("y"), Close, Sp, F.Id("goldenProjectiveMultiplier"), Sp, D(0)));

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
