using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class FixedPointSemiconjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Bridges/FixedPointSemiconjugacy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semiconjugate bridges transport fixed points and stable fibers.",
        H("Fixed Point Semiconjugacy"),
        Blocks(
            Theorem(
                "fixed-point-maps",
                "fixed_point_maps",
                FixedPointMapsFormula(),
                "Fixed Point Maps",
                "A fixed point is transported through every semiconjugate bridge.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "fixed-point-reflects-of-injective",
                "fixed_point_reflects_of_injective",
                FixedPointReflectsOfInjectiveFormula(),
                "Fixed Point Reflects Of Injective",
                "An injective semiconjugate bridge also reflects fixed points.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "fixed-point-iff-of-injective",
                "fixed_point_iff_of_injective",
                FixedPointIffOfInjectiveFormula(),
                "Fixed Point iff Of Injective",
                "Under an injective semiconjugacy, fixedness is exactly preserved.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "observation-fiber-forward-invariant",
                "observation_fiber_forward_invariant",
                ObservationFiberForwardInvariantFormula(),
                "Observation Fiber Forward Invariant",
                "Equality under the observer remains equal after one semiconjugate step.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "semiconjugacy-iterate",
                "semiconjugacy_iterate",
                SemiconjugacyIterateFormula(),
                "Semiconjugacy Iterate",
                "Semiconjugacy transports every finite iterate, not only one step.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "fixed-point-maps-across-composite",
                "fixed_point_maps_across_composite",
                FixedPointMapsAcrossCompositeFormula(),
                "Fixed Point Maps Across Composite",
                "Fixed-point transport composes along two observer bridges.",
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

private static Formula FixedPointMapsFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Y")))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("X")))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("x")), Seq(F.Id("X")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep")), Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("sourceStep"), Sp, F.Id("x"))],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("targetStep"), Sp, Open, F.Id("bridge"), Sp, F.Id("x"), Close));

private static Formula FixedPointReflectsOfInjectiveFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Y")))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("X")))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("x")), Seq(F.Id("X")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep")), Seq(F.Id("Function"), Dot, F.Id("Injective"), Sp, F.Id("bridge")), Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("targetStep"), Sp, Open, F.Id("bridge"), Sp, F.Id("x"), Close)],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("sourceStep"), Sp, F.Id("x")));

private static Formula FixedPointIffOfInjectiveFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Y")))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("X")))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("x")), Seq(F.Id("X")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep")), Seq(F.Id("Function"), Dot, F.Id("Injective"), Sp, F.Id("bridge"))],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("sourceStep"), Sp, F.Id("x"), Sp, Leftrightarrow, Sp, F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("targetStep"), Sp, Open, F.Id("bridge"), Sp, F.Id("x"), Close));

private static Formula ObservationFiberForwardInvariantFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Y")))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("X")))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("x"), Underscore, Grp(D(1))), Seq(F.Id("X"))), Typed(Seq(F.Id("x"), Underscore, Grp(D(2))), Seq(F.Id("X")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep")), Seq(F.Id("bridge"), Sp, F.Id("x"), Underscore, Grp(D(1)), Sp, Eq, Sp, F.Id("bridge"), Sp, F.Id("x"), Underscore, Grp(D(2)))],
        Seq(F.Id("bridge"), Sp, Open, F.Id("sourceStep"), Sp, F.Id("x"), Underscore, Grp(D(1)), Close, Sp, Eq, Sp, F.Id("bridge"), Sp, Open, F.Id("sourceStep"), Sp, F.Id("x"), Underscore, Grp(D(2)), Close));

private static Formula SemiconjugacyIterateFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Y")))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("X")))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("n")), Seq(Mathbb, Grp(F.Id("N")))), Typed(Seq(F.Id("x")), Seq(F.Id("X")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep"))],
        Seq(F.Id("bridge"), Sp, Open, Open, F.Id("sourceStep"), Caret, Grp(OpenBracket, F.Id("n"), CloseBracket), Close, Sp, F.Id("x"), Close, Sp, Eq, Sp, Open, F.Id("targetStep"), Caret, Grp(OpenBracket, F.Id("n"), CloseBracket), Close, Sp, Open, F.Id("bridge"), Sp, F.Id("x"), Close));

private static Formula FixedPointMapsAcrossCompositeFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Z")), Seq(F.Id("Type"))), Typed(Seq(F.Id("firstBridge")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Y")))), Typed(Seq(F.Id("secondBridge")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Z")))), Typed(Seq(F.Id("firstStep")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("X")))), Typed(Seq(F.Id("secondStep")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Y")))), Typed(Seq(F.Id("thirdStep")), new Formula.TypeArrow(Seq(F.Id("Z")), Seq(F.Id("Z")))), Typed(Seq(F.Id("x")), Seq(F.Id("X")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("firstBridge"), Sp, F.Id("firstStep"), Sp, F.Id("secondStep")), Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("secondBridge"), Sp, F.Id("secondStep"), Sp, F.Id("thirdStep")), Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("firstStep"), Sp, F.Id("x"))],
        Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("thirdStep"), Sp, Open, Open, F.Id("secondBridge"), Sp, Circ, Sp, F.Id("firstBridge"), Close, Sp, F.Id("x"), Close));

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
