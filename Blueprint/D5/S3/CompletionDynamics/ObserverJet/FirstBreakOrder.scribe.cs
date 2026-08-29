using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.ObserverJet;

internal sealed class FirstBreakOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/ObserverJet/FirstBreakOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first nonzero normal jet order is totalized in WithTop Nat, with infinity recording threads whose every finite jet remains unbroken.",
        H("First Break Order"),
        Blocks(
            Theorem(
                "first-break-order-eq-top-iff",
                "first_break_order_eq_top_iff",
                FirstBreakOrderEqTopIffFormula(),
                "First Break Order eq Top iff",
                "Absence of every positive finite break is represented exactly by ⊤.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "first-break-order-of-exists",
                "first_break_order_of_exists",
                FirstBreakOrderOfExistsFormula(),
                "First Break Order Of Exists",
                "Under an existence witness, the totalized order is the ordinary least natural-number witness.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "first-break-order-spec",
                "first_break_order_spec",
                FirstBreakOrderSpecFormula(),
                "First Break Order Spec",
                "The selected finite order is a genuine positive break.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "no-break-before-first",
                "no_break_before_first",
                NoBreakBeforeFirstFormula(),
                "No Break Before First",
                "No smaller order is an admissible break.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "first-order-break-characterization",
                "first_order_break_characterization",
                FirstOrderBreakCharacterizationFormula(),
                "First Order Break Characterization",
                "A first-order break means that order one is the least positive nonzero jet.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "quadratic-break-characterization",
                "quadratic_break_characterization",
                QuadraticBreakCharacterizationFormula(),
                "Quadratic Break Characterization",
                "If order one vanishes and order two breaks, the first break is quadratic.",
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

private static Formula FirstBreakOrderEqTopIffFormula() => Statement(
    [Typed(Seq(F.Id("breaks")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("N"))), Seq(F.Id("Prop"))))],
        [],
        [],
        Seq(F.Id("firstBreakOrder"), Sp, F.Id("breaks"), Sp, Eq, Sp, F.Id("top"), Sp, Leftrightarrow, Sp, Neg, Sp, Exists, Sp, F.Id("k"), Comma, Sp, F.Id("IsBreakOrder"), Sp, F.Id("breaks"), Sp, F.Id("k")));

private static Formula FirstBreakOrderOfExistsFormula() => Statement(
    [Typed(Seq(F.Id("breaks")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("N"))), Seq(F.Id("Prop"))))],
        [],
        [Seq(Exists, Sp, F.Id("k"), Comma, Sp, F.Id("IsBreakOrder"), Sp, F.Id("breaks"), Sp, F.Id("k"))],
        Seq(F.Id("firstBreakOrder"), Sp, F.Id("breaks"), Sp, Eq, Sp, Open, Mathbb, Grp(F.Id("N")), Dot, F.Id("find"), Sp, F.Id("h"), Sp, Colon, Sp, F.Id("WithTop"), Sp, Mathbb, Grp(F.Id("N")), Close));

private static Formula FirstBreakOrderSpecFormula() => Statement(
    [Typed(Seq(F.Id("breaks")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("N"))), Seq(F.Id("Prop"))))],
        [],
        [Seq(Exists, Sp, F.Id("k"), Comma, Sp, F.Id("IsBreakOrder"), Sp, F.Id("breaks"), Sp, F.Id("k"))],
        Seq(F.Id("IsBreakOrder"), Sp, F.Id("breaks"), Sp, Open, Mathbb, Grp(F.Id("N")), Dot, F.Id("find"), Sp, F.Id("h"), Close));

private static Formula NoBreakBeforeFirstFormula() => Statement(
    [Typed(Seq(F.Id("breaks")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("N"))), Seq(F.Id("Prop")))), Typed(Seq(F.Id("j")), Seq(Mathbb, Grp(F.Id("N"))))],
        [],
        [Seq(Exists, Sp, F.Id("k"), Comma, Sp, F.Id("IsBreakOrder"), Sp, F.Id("breaks"), Sp, F.Id("k")), Seq(F.Id("j"), Sp, Lt, Sp, Mathbb, Grp(F.Id("N")), Dot, F.Id("find"), Sp, F.Id("h"))],
        Seq(Neg, Sp, F.Id("IsBreakOrder"), Sp, F.Id("breaks"), Sp, F.Id("j")));

private static Formula FirstOrderBreakCharacterizationFormula() => Statement(
    [Typed(Seq(F.Id("breaks")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("N"))), Seq(F.Id("Prop"))))],
        [],
        [Seq(F.Id("breaks"), Sp, D(1))],
        Seq(F.Id("firstBreakOrder"), Sp, F.Id("breaks"), Sp, Eq, Sp, Open, D(1), Sp, Colon, Sp, F.Id("WithTop"), Sp, Mathbb, Grp(F.Id("N")), Close));

private static Formula QuadraticBreakCharacterizationFormula() => Statement(
    [Typed(Seq(F.Id("breaks")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("N"))), Seq(F.Id("Prop"))))],
        [],
        [Seq(Neg, Sp, F.Id("breaks"), Sp, D(1)), Seq(F.Id("breaks"), Sp, D(2))],
        Seq(F.Id("firstBreakOrder"), Sp, F.Id("breaks"), Sp, Eq, Sp, Open, D(2), Sp, Colon, Sp, F.Id("WithTop"), Sp, Mathbb, Grp(F.Id("N")), Close));

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
