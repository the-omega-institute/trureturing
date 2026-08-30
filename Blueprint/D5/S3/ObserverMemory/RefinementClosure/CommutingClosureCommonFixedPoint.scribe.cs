using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class CommutingClosureCommonFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two commuting closure operators compose to a closure whose fixed points are exactly their common fixed points.",
        H("Commuting Closure Common Fixed Point"),
        Blocks(
            Theorem(
                "commuting-composition-apply",
                "commutingComposition_apply",
                CommutingcompositionApplyFormula(),
                "Commuting Composition Apply",
                "This theorem establishes commuting composition apply in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "commuting-closure-composition-fixed-iff",
                "commuting_closure_composition_fixed_iff",
                CommutingClosureCompositionFixedIffFormula(),
                "Commuting Closure Composition Fixed iff",
                "A point is fixed by the commuting composition exactly when it is fixed by both constituent closures.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "commuting-composition-order-independent",
                "commuting_composition_order_independent",
                CommutingCompositionOrderIndependentFormula(),
                "Commuting Composition Order Independent",
                "Commutativity makes the one-pass common closure independent of order.",
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

private static Formula CommutingcompositionApplyFormula() => Statement(
    [Typed(Seq(F.Id("alpha")), Seq(F.Id("Type"))), Typed(Seq(F.Id("first")), Seq(F.Id("ClosureOperator"), Sp, F.Id("alpha"))), Typed(Seq(F.Id("second")), Seq(F.Id("ClosureOperator"), Sp, F.Id("alpha"))), Typed(Seq(F.Id("x")), Seq(F.Id("alpha")))],
        [Seq(OpenBracket, Call("PartialOrder", Seq(F.Id("alpha"))), CloseBracket)],
        [Seq(F.Id("Function"), Dot, F.Id("Commute"), Sp, F.Id("first"), Sp, F.Id("second"))],
        Seq(F.Id("commutingComposition"), Sp, F.Id("first"), Sp, F.Id("second"), Sp, F.Id("commute"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("first"), Sp, Open, F.Id("second"), Sp, F.Id("x"), Close));

private static Formula CommutingClosureCompositionFixedIffFormula() => Statement(
    [Typed(Seq(F.Id("alpha")), Seq(F.Id("Type"))), Typed(Seq(F.Id("first")), Seq(F.Id("ClosureOperator"), Sp, F.Id("alpha"))), Typed(Seq(F.Id("second")), Seq(F.Id("ClosureOperator"), Sp, F.Id("alpha"))), Typed(Seq(F.Id("x")), Seq(F.Id("alpha")))],
        [Seq(OpenBracket, Call("PartialOrder", Seq(F.Id("alpha"))), CloseBracket)],
        [Seq(F.Id("Function"), Dot, F.Id("Commute"), Sp, F.Id("first"), Sp, F.Id("second"))],
        Seq(F.Id("commutingComposition"), Sp, F.Id("first"), Sp, F.Id("second"), Sp, F.Id("commute"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("x"), Sp, Leftrightarrow, Sp, F.Id("first"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("x"), Sp, Land, Sp, F.Id("second"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("x")));

private static Formula CommutingCompositionOrderIndependentFormula() => Statement(
    [Typed(Seq(F.Id("alpha")), Seq(F.Id("Type"))), Typed(Seq(F.Id("first")), Seq(F.Id("ClosureOperator"), Sp, F.Id("alpha"))), Typed(Seq(F.Id("second")), Seq(F.Id("ClosureOperator"), Sp, F.Id("alpha"))), Typed(Seq(F.Id("x")), Seq(F.Id("alpha")))],
        [Seq(OpenBracket, Call("PartialOrder", Seq(F.Id("alpha"))), CloseBracket)],
        [Seq(F.Id("Function"), Dot, F.Id("Commute"), Sp, F.Id("first"), Sp, F.Id("second"))],
        Seq(F.Id("commutingComposition"), Sp, F.Id("first"), Sp, F.Id("second"), Sp, F.Id("commute"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("commutingComposition"), Sp, F.Id("second"), Sp, F.Id("first"), Sp, F.Id("commute"), Dot, F.Id("symm"), Sp, F.Id("x")));

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
