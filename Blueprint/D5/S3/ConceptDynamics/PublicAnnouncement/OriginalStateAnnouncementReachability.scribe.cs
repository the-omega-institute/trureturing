using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PublicAnnouncement;

internal sealed class OriginalStateAnnouncementReachabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A true announcement is preserved along every restricted access path.",
        H("Public Announcement on the Original State Carrier"),
        Blocks(Describe.Lean(
            DescribeId.Create(
                "true-public-announcement-is-common-knowledge-on-original-states"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/PublicAnnouncement/"
                    + "OriginalStateAnnouncementReachability."
                    + "true_public_announcement_is_common_knowledge_on_original_states"),
            H("True public announcements create common knowledge"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The post-announcement accessibility relation is displayed directly: "
                        + "both endpoints satisfy the public predicate and some agent relates "
                        + "the source endpoint to the target endpoint.")),
                Paragraph(Text(
                    "The state carrier remains the original State type. The actual anchor's "
                        + "truth is a public premise, and common knowledge quantifies over every "
                        + "state in the reflexive-transitive closure of the restricted relation.")),
                Paragraph(Text(
                    "The proof inducts on the supplied ReflTransGen path. The reflexive case "
                        + "uses the true-anchor premise, while a nontrivial final step carries "
                        + "the target predicate as part of the announcement restriction."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("State");
        Formula agent = F.Id("Agent");
        Formula access = F.Id("access");
        Formula predicate = F.Id("P");
        Formula anchor = F.Id("a");
        Formula source = F.Id("s");
        Formula target = F.Id("t");
        Formula actingAgent = F.Id("i");
        Formula proposition = F.Id("Prop");
        Formula restrictedAccess = Seq(
            Open, LambdaLower, Sp, source, Comma, Sp, target, Sp, Mapsto, Sp,
            Apply("P", source), Sp, Land, Sp,
            Apply("P", target), Sp, Land, Sp,
            Exists, Sp, actingAgent, Colon, Sp, agent, Comma, Sp,
            Apply("access", actingAgent, source, target), Close);
        Formula reachable = Apply(
            "ReflTransGen", restrictedAccess, anchor, target);
        Formula commonKnowledge = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("t"),
            state,
            new Formula.Logic(
                reachable,
                FormulaLogicOperator.Implies,
                Apply("P", target)));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, agent, Colon, Sp, F.Id("Type"), Comma, Sp,
            access, Colon, Sp,
            Arrow(agent, Arrow(state, Arrow(state, proposition))), Comma, RowBreak, Grp(),
            predicate, Colon, Sp, Arrow(state, proposition), Comma, Sp,
            anchor, Colon, Sp, state, Comma, RowBreak, Grp(),
            Apply("P", anchor), Sp, Rightarrow, RowBreak, Grp(),
            commonKnowledge, Dot));
    }
}
