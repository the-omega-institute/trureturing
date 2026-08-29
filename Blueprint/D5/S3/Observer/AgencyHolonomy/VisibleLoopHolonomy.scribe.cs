using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class VisibleLoopHolonomyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/AgencyHolonomy/VisibleLoopHolonomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointed holonomy is a visible return with nontrivial hidden transport; strategy factorization hides policy drift, while a faithful joint readout rules out hidden loops.",
        H("Visible Loop Holonomy"),
        Blocks(
            Theorem(
                "visible-loop-policy-change-witnesses-pointed-holonomy",
                "visible_loop_policy_change_witnesses_pointed_holonomy",
                VisibleLoopPolicyChangeWitnessesPointedHolonomyFormula(),
                "Visible Loop Policy Change Witnesses Pointed Holonomy",
                "Strategy change on a visible loop certifies pointed holonomy, including both the visible-return and hidden-transport clauses.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "visible-loop-policy-change-implies-nontrivial-transport",
                "visible_loop_policy_change_implies_nontrivial_transport",
                VisibleLoopPolicyChangeImpliesNontrivialTransportFormula(),
                "Visible Loop Policy Change Implies Nontrivial Transport",
                "The hidden-transport component of the pointed-holonomy witness.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "strategy-factorization-makes-visible-loops-invisible",
                "strategy_factorization_makes_visible_loops_invisible",
                StrategyFactorizationMakesVisibleLoopsInvisibleFormula(),
                "Strategy Factorization Makes Visible Loops Invisible",
                "If strategy factors through the visible readout, every visible loop is strategy-invisible.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "faithful-joint-readout-kills-hidden-holonomy",
                "faithful_joint_readout_kills_hidden_holonomy",
                FaithfulJointReadoutKillsHiddenHolonomyFormula(),
                "Faithful Joint Readout Kills Hidden Holonomy",
                "A joint current-strategy readout that is injective rules out any nontrivial transport hidden from both coordinates.",
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

private static Formula VisibleLoopPolicyChangeWitnessesPointedHolonomyFormula() => Statement(
    [Typed(Seq(F.Id("U")), Seq(F.Id("Type"))), Typed(Seq(F.Id("H")), Seq(F.Id("Type"))), Typed(Seq(F.Id("B")), Seq(F.Id("Type"))), Typed(Seq(F.Id("P")), Seq(F.Id("Type"))), Typed(Seq(F.Id("update")), new Formula.TypeArrow(Seq(F.Id("U")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("H"))))), Typed(Seq(F.Id("readout")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("B")))), Typed(Seq(F.Id("strategy")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("P")))), Typed(Seq(F.Id("word")), Seq(F.Id("List"), Sp, F.Id("U"))), Typed(Seq(F.Id("state")), Seq(F.Id("H")))],
        [],
        [Seq(F.Id("VisibleLoopAt"), Sp, F.Id("update"), Sp, F.Id("readout"), Sp, F.Id("word"), Sp, F.Id("state")), Seq(F.Id("StrategyVisibleHolonomyAt"), Sp, F.Id("update"), Sp, F.Id("strategy"), Sp, F.Id("word"), Sp, F.Id("state"))],
        Seq(F.Id("PointedHolonomyAt"), Sp, F.Id("update"), Sp, F.Id("readout"), Sp, F.Id("word"), Sp, F.Id("state")));

private static Formula VisibleLoopPolicyChangeImpliesNontrivialTransportFormula() => Statement(
    [Typed(Seq(F.Id("U")), Seq(F.Id("Type"))), Typed(Seq(F.Id("H")), Seq(F.Id("Type"))), Typed(Seq(F.Id("B")), Seq(F.Id("Type"))), Typed(Seq(F.Id("P")), Seq(F.Id("Type"))), Typed(Seq(F.Id("update")), new Formula.TypeArrow(Seq(F.Id("U")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("H"))))), Typed(Seq(F.Id("readout")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("B")))), Typed(Seq(F.Id("strategy")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("P")))), Typed(Seq(F.Id("word")), Seq(F.Id("List"), Sp, F.Id("U"))), Typed(Seq(F.Id("state")), Seq(F.Id("H")))],
        [],
        [Seq(F.Id("VisibleLoopAt"), Sp, F.Id("update"), Sp, F.Id("readout"), Sp, F.Id("word"), Sp, F.Id("state")), Seq(F.Id("StrategyVisibleHolonomyAt"), Sp, F.Id("update"), Sp, F.Id("strategy"), Sp, F.Id("word"), Sp, F.Id("state"))],
        Seq(F.Id("NontrivialTransportAt"), Sp, F.Id("update"), Sp, F.Id("word"), Sp, F.Id("state")));

private static Formula StrategyFactorizationMakesVisibleLoopsInvisibleFormula() => Statement(
    [Typed(Seq(F.Id("U")), Seq(F.Id("Type"))), Typed(Seq(F.Id("H")), Seq(F.Id("Type"))), Typed(Seq(F.Id("B")), Seq(F.Id("Type"))), Typed(Seq(F.Id("P")), Seq(F.Id("Type"))), Typed(Seq(F.Id("update")), new Formula.TypeArrow(Seq(F.Id("U")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("H"))))), Typed(Seq(F.Id("readout")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("B")))), Typed(Seq(F.Id("strategy")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("P")))), Typed(Seq(F.Id("factor")), new Formula.TypeArrow(Seq(F.Id("B")), Seq(F.Id("P")))), Typed(Seq(F.Id("word")), Seq(F.Id("List"), Sp, F.Id("U"))), Typed(Seq(F.Id("state")), Seq(F.Id("H")))],
        [],
        [Seq(Forall, Sp, F.Id("state"), Comma, Sp, F.Id("strategy"), Sp, F.Id("state"), Sp, Eq, Sp, F.Id("factor"), Sp, Open, F.Id("readout"), Sp, F.Id("state"), Close), Seq(F.Id("VisibleLoopAt"), Sp, F.Id("update"), Sp, F.Id("readout"), Sp, F.Id("word"), Sp, F.Id("state"))],
        Seq(F.Id("strategy"), Sp, Open, F.Id("runWord"), Sp, F.Id("update"), Sp, F.Id("word"), Sp, F.Id("state"), Close, Sp, Eq, Sp, F.Id("strategy"), Sp, F.Id("state")));

private static Formula FaithfulJointReadoutKillsHiddenHolonomyFormula() => Statement(
    [Typed(Seq(F.Id("U")), Seq(F.Id("Type"))), Typed(Seq(F.Id("H")), Seq(F.Id("Type"))), Typed(Seq(F.Id("B")), Seq(F.Id("Type"))), Typed(Seq(F.Id("P")), Seq(F.Id("Type"))), Typed(Seq(F.Id("update")), new Formula.TypeArrow(Seq(F.Id("U")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("H"))))), Typed(Seq(F.Id("readout")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("B")))), Typed(Seq(F.Id("strategy")), new Formula.TypeArrow(Seq(F.Id("H")), Seq(F.Id("P")))), Typed(Seq(F.Id("word")), Seq(F.Id("List"), Sp, F.Id("U"))), Typed(Seq(F.Id("state")), Seq(F.Id("H")))],
        [],
        [Seq(F.Id("Function"), Dot, F.Id("Injective"), Sp, Open, F.Id("agencyEnrichment"), Sp, F.Id("readout"), Sp, F.Id("strategy"), Close), Seq(F.Id("VisibleLoopAt"), Sp, F.Id("update"), Sp, F.Id("readout"), Sp, F.Id("word"), Sp, F.Id("state")), Seq(F.Id("strategy"), Sp, Open, F.Id("runWord"), Sp, F.Id("update"), Sp, F.Id("word"), Sp, F.Id("state"), Close, Sp, Eq, Sp, F.Id("strategy"), Sp, F.Id("state"))],
        Seq(F.Id("runWord"), Sp, F.Id("update"), Sp, F.Id("word"), Sp, F.Id("state"), Sp, Eq, Sp, F.Id("state")));

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
