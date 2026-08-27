using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PublicAnnouncement;

internal sealed class AdmissibleAnnouncementCommonKnowledgeDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/PublicAnnouncement/"
            + "AdmissibleAnnouncementCommonKnowledge."
            + "true_public_announcement_is_common_knowledge_on_admitted_domain";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A true public announcement creates common knowledge on the restricted admitted domain.",
        H("Common Knowledge on an Admissible Announcement Domain"),
        Blocks(Describe.Lean(
            DescribeId.Create(
                "true-public-announcement-common-knowledge-admitted-domain"),
            DeclarationHandle.Create(Declaration),
            H("True public announcements create common knowledge"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The pre-announcement admitted domain A and public proposition P are "
                        + "both public inputs. The post-announcement carrier is constructed "
                        + "by the canonical descriptiveCondition(P,A) restriction.")),
                Paragraph(Text(
                    "Common reachability is the reflexive-transitive closure of steps "
                        + "witnessed by one agent's accessibility relation. Every target "
                        + "in the restricted carrier satisfies P by its membership evidence.")),
                Paragraph(Text(
                    "The actual anchor is required to lie in A and P, so it embeds into the "
                        + "post-announcement carrier without replacing A by the universal set."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("State");
        Formula agent = F.Id("Agent");
        Formula admitted = F.Id("A");
        Formula predicate = F.Id("P");
        Formula access = F.Id("access");
        Formula anchor = F.Id("a");
        Formula actual = F.Id("aPrime");
        Formula source = F.Id("s");
        Formula target = F.Id("t");
        Formula actingAgent = F.Id("i");
        Formula proposition = F.Id("Prop");
        Formula stateSet = Call("Set", state);
        Formula announced = Call(
            "Subtype", Call("descriptiveCondition", predicate, admitted));
        Formula accessType = new Formula.TypeArrow(
            agent,
            new Formula.TypeArrow(
                state,
                new Formula.TypeArrow(state, proposition)));
        Formula step = Seq(
            Open, LambdaLower, Sp, source, Comma, Sp, target, Sp, Mapsto, Sp,
            Exists, Sp, actingAgent, Colon, Sp, agent, Comma, Sp,
            Call("access", actingAgent, Call("fst", source), Call("fst", target)),
            Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Comma, Sp, agent, Colon, Sp, F.Id("Type"), Comma),
            Seq(
                admitted, Comma, Sp, predicate, Colon, Sp, stateSet, Comma, Sp,
                access, Colon, Sp, accessType, Comma, Sp,
                anchor, Colon, Sp, state, Comma),
            Seq(
                anchor, InMacro, Sp, admitted, Sp, Land, Sp,
                anchor, InMacro, Sp, predicate, Sp, Rightarrow),
            Seq(
                Exists, Sp, actual, Colon, Sp, announced, Comma, Sp,
                Call("fst", actual), Sp, Eq, Sp, anchor, Sp, Land, Sp),
            Seq(
                Forall, Sp, target, Colon, Sp, announced, Comma, Sp,
                Call("ReflTransGen", step, actual, target), Sp, Rightarrow, Sp,
                Call("fst", target), InMacro, Sp, predicate, Dot),
        ]));
    }
}
