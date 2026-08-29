using static StrataLint.Scribe.DefinitionDsl;

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
                "Visible Loop Policy Change Witnesses Pointed Holonomy",
                "Strategy change on a visible loop certifies pointed holonomy, including both the visible-return and hidden-transport clauses.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "visible-loop-policy-change-implies-nontrivial-transport",
                "visible_loop_policy_change_implies_nontrivial_transport",
                "Visible Loop Policy Change Implies Nontrivial Transport",
                "The hidden-transport component of the pointed-holonomy witness.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "strategy-factorization-makes-visible-loops-invisible",
                "strategy_factorization_makes_visible_loops_invisible",
                "Strategy Factorization Makes Visible Loops Invisible",
                "If strategy factors through the visible readout, every visible loop is strategy-invisible.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "faithful-joint-readout-kills-hidden-holonomy",
                "faithful_joint_readout_kills_hidden_holonomy",
                "Faithful Joint Readout Kills Hidden Holonomy",
                "A joint current-strategy readout that is injective rules out any nontrivial transport hidden from both coordinates.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);
}
