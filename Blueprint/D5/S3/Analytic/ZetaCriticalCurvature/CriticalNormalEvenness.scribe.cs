using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCriticalCurvature;

internal sealed class CriticalNormalEvennessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ZetaCriticalCurvature/CriticalNormalEvenness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection-even scalar potentials have zero first normal derivative at the fixed axis.",
        H("Critical Normal Evenness"),
        Blocks(
            Theorem(
                "even-has-deriv-at-zero",
                "even_hasDerivAt_zero",
                EvenHasderivatZeroFormula(),
                "Even Has Deriv At Zero",
                "A differentiable even real function has zero derivative at the reflection fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "deriv-even-zero",
                "deriv_even_zero",
                DerivEvenZeroFormula(),
                "Deriv Even Zero",
                "deriv formulation of the same reflection obstruction.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "critical-normal-derivative-zero",
                "critical_normal_derivative_zero",
                CriticalNormalDerivativeZeroFormula(),
                "Critical Normal Derivative Zero",
                "Parameterized potential version. For every fixed tangential coordinate t, normal reflection symmetry removes the first normal derivative.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "critical-normal-deriv-zero",
                "critical_normal_deriv_zero",
                CriticalNormalDerivZeroFormula(),
                "Critical Normal Deriv Zero",
                "Pointwise family formulation.",
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

private static Formula EvenHasderivatZeroFormula() => Statement(
    [Typed(Seq(F.Id("V")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("d")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("HasDerivAt"), Sp, F.Id("V"), Sp, F.Id("d"), Sp, D(0)), Seq(Forall, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, F.Id("V"), Sp, Open, Minus, F.Id("u"), Close, Sp, Eq, Sp, F.Id("V"), Sp, F.Id("u"))],
        Seq(F.Id("d"), Sp, Eq, Sp, D(0)));

private static Formula DerivEvenZeroFormula() => Statement(
    [Typed(Seq(F.Id("V")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R")))))],
        [],
        [Seq(F.Id("DifferentiableAt"), Sp, Mathbb, Grp(F.Id("R")), Sp, F.Id("V"), Sp, D(0)), Seq(Forall, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, F.Id("V"), Sp, Open, Minus, F.Id("u"), Close, Sp, Eq, Sp, F.Id("V"), Sp, F.Id("u"))],
        Seq(F.Id("deriv"), Sp, F.Id("V"), Sp, D(0), Sp, Eq, Sp, D(0)));

private static Formula CriticalNormalDerivativeZeroFormula() => Statement(
    [Typed(Seq(F.Id("V")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R")))))), Typed(Seq(F.Id("t")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("d")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("HasDerivAt"), Sp, Open, LambdaLower, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, F.Id("V"), Sp, F.Id("u"), Sp, F.Id("t"), Close, Sp, F.Id("d"), Sp, D(0)), Seq(Forall, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, F.Id("V"), Sp, Open, Minus, F.Id("u"), Close, Sp, F.Id("t"), Sp, Eq, Sp, F.Id("V"), Sp, F.Id("u"), Sp, F.Id("t"))],
        Seq(F.Id("d"), Sp, Eq, Sp, D(0)));

private static Formula CriticalNormalDerivZeroFormula() => Statement(
    [Typed(Seq(F.Id("V")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))))],
        [],
        [Seq(Forall, Sp, F.Id("t"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, F.Id("DifferentiableAt"), Sp, Mathbb, Grp(F.Id("R")), Sp, Open, LambdaLower, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, F.Id("V"), Sp, F.Id("u"), Sp, F.Id("t"), Close, Sp, D(0)), Seq(Forall, Sp, F.Id("u"), Sp, F.Id("t"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, F.Id("V"), Sp, Open, Minus, F.Id("u"), Close, Sp, F.Id("t"), Sp, Eq, Sp, F.Id("V"), Sp, F.Id("u"), Sp, F.Id("t"))],
        Seq(Forall, Sp, F.Id("t"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, F.Id("deriv"), Sp, Open, LambdaLower, Sp, F.Id("u"), Sp, Colon, Sp, Mathbb, Grp(F.Id("R")), Sp, Mapsto, Sp, F.Id("V"), Sp, F.Id("u"), Sp, F.Id("t"), Close, Sp, D(0), Sp, Eq, Sp, D(0)));

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
