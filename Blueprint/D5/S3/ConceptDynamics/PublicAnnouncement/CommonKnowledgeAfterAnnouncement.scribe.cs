using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PublicAnnouncement;

internal sealed class CommonKnowledgeAfterAnnouncementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A true public announcement makes its announced proposition common knowledge.",
        H("Common Knowledge After Public Announcement"),
        Blocks(Describe.Lean(
            DescribeId.Create("true-public-announcement-is-common-knowledge"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/PublicAnnouncement/CommonKnowledgeAfterAnnouncement."
                    + "true_public_announcement_is_common_knowledge"),
            H("True public announcements create common knowledge"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state carrier is built by applying the repository's canonical "
                        + "descriptive announcement restriction to the universal model.")),
                Paragraph(Text(
                    "An arbitrary agent accessibility relation is retained on the announced "
                        + "subtype, and common knowledge is the proposition at every state in "
                        + "the reflexive-transitive finite path closure from the actual anchor.")),
                Paragraph(Text(
                    "Because every post-announcement representative carries the public "
                        + "predicate as its subtype evidence, every iterated information path "
                        + "satisfies that predicate. Repository searches found no exact packaged "
                        + "public-announcement/common-knowledge theorem; Mathlib's "
                        + "Relation.ReflTransGen is applied for path closure."))),
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
        Formula announcedActual = F.Id("aPrime");
        Formula target = F.Id("x");
        Formula stateType = F.Id("Type");
        Formula proposition = F.Id("Prop");
        Formula model = Apply("announcedModel", predicate);
        Formula step = Apply("announcementStep", access);
        Formula actualEquality = new Formula.Relation(
            Apply("fst", announcedActual), FormulaRelationOperator.Equal, anchor);
        Formula commonKnowledge = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            model,
            new Formula.Logic(
                Apply("ReflTransGen", step, announcedActual, target),
                FormulaLogicOperator.Implies,
                Apply("P", Apply("fst", target))));
        Formula announcedWitness = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("aPrime"),
            model,
            new Formula.Logic(actualEquality, FormulaLogicOperator.And, commonKnowledge));
        Formula types = Seq(
            state, Comma, Sp, agent, Colon, Sp, stateType, Comma, Sp,
            access, Colon, Sp,
            Arrow(agent, Arrow(state, Arrow(state, proposition))), Comma, Sp,
            predicate, Colon, Sp, Arrow(state, proposition), Comma, Sp,
            anchor, Colon, Sp, state);

        return Disp(Seq(
            Forall, Sp, types, Comma, RowBreak, Grp(),
            Apply("P", anchor), Sp, Rightarrow, RowBreak, Grp(),
            announcedWitness, Dot));
    }
}
