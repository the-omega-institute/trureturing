using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class DifferentiableFixedPointConjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Bridges/DifferentiableFixedPointConjugacy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nondegenerate differentiable bridges preserve local multipliers.",
        H("Differentiable Fixed Point Conjugacy"),
        Blocks(
            Theorem(
                "derivative-intertwining-at-fixed-point",
                "derivative_intertwining_at_fixed_point",
                DerivativeIntertwiningAtFixedPointFormula(),
                "Derivative Intertwining At Fixed Point",
                "The chain rule intertwines the two local multipliers at a fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "multiplier-eq-of-nondegenerate-bridge",
                "multiplier_eq_of_nondegenerate_bridge",
                MultiplierEqOfNondegenerateBridgeFormula(),
                "Multiplier eq Of Nondegenerate Bridge",
                "A nonzero bridge derivative forces equality of local multipliers.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "attracting-multiplier-iff",
                "attracting_multiplier_iff",
                AttractingMultiplierIffFormula(),
                "Attracting Multiplier iff",
                "Strict attraction is preserved by a nondegenerate bridge.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "neutral-multiplier-iff",
                "neutral_multiplier_iff",
                NeutralMultiplierIffFormula(),
                "Neutral Multiplier iff",
                "Neutrality is preserved by a nondegenerate bridge.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "repelling-multiplier-iff",
                "repelling_multiplier_iff",
                RepellingMultiplierIffFormula(),
                "Repelling Multiplier iff",
                "Repulsion is preserved by a nondegenerate bridge.",
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

private static Formula DerivativeIntertwiningAtFixedPointFormula() => Statement(
    [Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dBridge")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dSource")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dTarget")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep")), Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("sourceStep"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("bridge"), Sp, F.Id("dBridge"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("sourceStep"), Sp, F.Id("dSource"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("targetStep"), Sp, F.Id("dTarget"), Sp, Open, F.Id("bridge"), Sp, F.Id("x"), Close)],
        Seq(F.Id("dBridge"), Sp, Times, Sp, F.Id("dSource"), Sp, Eq, Sp, F.Id("dTarget"), Sp, Times, Sp, F.Id("dBridge")));

private static Formula MultiplierEqOfNondegenerateBridgeFormula() => Statement(
    [Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dBridge")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dSource")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dTarget")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep")), Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("sourceStep"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("bridge"), Sp, F.Id("dBridge"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("sourceStep"), Sp, F.Id("dSource"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("targetStep"), Sp, F.Id("dTarget"), Sp, Open, F.Id("bridge"), Sp, F.Id("x"), Close), Seq(F.Id("dBridge"), Sp, Neq, Sp, D(0))],
        Seq(F.Id("dSource"), Sp, Eq, Sp, F.Id("dTarget")));

private static Formula AttractingMultiplierIffFormula() => Statement(
    [Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dBridge")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dSource")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dTarget")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep")), Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("sourceStep"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("bridge"), Sp, F.Id("dBridge"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("sourceStep"), Sp, F.Id("dSource"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("targetStep"), Sp, F.Id("dTarget"), Sp, Open, F.Id("bridge"), Sp, F.Id("x"), Close), Seq(F.Id("dBridge"), Sp, Neq, Sp, D(0))],
        Seq(Bar, F.Id("dSource"), Bar, Sp, Lt, Sp, D(1), Sp, Leftrightarrow, Sp, Bar, F.Id("dTarget"), Bar, Sp, Lt, Sp, D(1)));

private static Formula NeutralMultiplierIffFormula() => Statement(
    [Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dBridge")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dSource")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dTarget")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep")), Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("sourceStep"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("bridge"), Sp, F.Id("dBridge"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("sourceStep"), Sp, F.Id("dSource"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("targetStep"), Sp, F.Id("dTarget"), Sp, Open, F.Id("bridge"), Sp, F.Id("x"), Close), Seq(F.Id("dBridge"), Sp, Neq, Sp, D(0))],
        Seq(Bar, F.Id("dSource"), Bar, Sp, Eq, Sp, D(1), Sp, Leftrightarrow, Sp, Bar, F.Id("dTarget"), Bar, Sp, Eq, Sp, D(1)));

private static Formula RepellingMultiplierIffFormula() => Statement(
    [Typed(Seq(F.Id("bridge")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("sourceStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("targetStep")), new Formula.TypeArrow(Seq(Mathbb, Grp(F.Id("R"))), Seq(Mathbb, Grp(F.Id("R"))))), Typed(Seq(F.Id("x")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dBridge")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dSource")), Seq(Mathbb, Grp(F.Id("R")))), Typed(Seq(F.Id("dTarget")), Seq(Mathbb, Grp(F.Id("R"))))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Semiconj"), Sp, F.Id("bridge"), Sp, F.Id("sourceStep"), Sp, F.Id("targetStep")), Seq(F.Id("Function"), Dot, F.Id("IsFixedPt"), Sp, F.Id("sourceStep"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("bridge"), Sp, F.Id("dBridge"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("sourceStep"), Sp, F.Id("dSource"), Sp, F.Id("x")), Seq(F.Id("HasDerivAt"), Sp, F.Id("targetStep"), Sp, F.Id("dTarget"), Sp, Open, F.Id("bridge"), Sp, F.Id("x"), Close), Seq(F.Id("dBridge"), Sp, Neq, Sp, D(0))],
        Seq(D(1), Sp, Lt, Sp, Bar, F.Id("dSource"), Bar, Sp, Leftrightarrow, Sp, D(1), Sp, Lt, Sp, Bar, F.Id("dTarget"), Bar));

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
