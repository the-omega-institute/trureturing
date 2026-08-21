using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class RobustKnowledgeConjunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Evidence-fiber-stable knowledge is closed under conjunction.",
        H("Robust Knowledge Conjunction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robust-knowledge"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction."
                        + "robustKnowledge"),
                H("Robust knowledge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A proposition is robustly known at an anchor when the anchor is admissible, "
                        + "the proposition holds there, and it holds at every admissible state "
                        + "with the same evidence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("robust-knowledge-conjunction"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeConjunction."
                        + "robust_knowledge_conjunction"),
                H("Knowledge conjunction"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The admissibility predicate, evidence map, proposition predicates, and "
                            + "anchor are independent source primitives.")),
                    Paragraph(Text(
                        "If each proposition is true throughout the anchor's admissible evidence "
                            + "fiber, both propositions are true throughout that same fiber, so "
                            + "their conjunction is robustly known.")),
                    Paragraph(Text(
                        "The proof directly unpacks the source predicate and introduces the two "
                            + "fiberwise facts; no witness structure or target-defined carrier is "
                            + "used."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula proposition = F.Id("Prop");
        Formula admissible = F.Id("Adm");
        Formula evidence = F.Id("E");
        Formula p = F.Id("P");
        Formula q = F.Id("Q");
        Formula anchor = F.Id("a");
        Formula x = F.Id("x");
        Formula pKnowledge = Apply("robustKnowledge", admissible, evidence, p, anchor);
        Formula qKnowledge = Apply("robustKnowledge", admissible, evidence, q, anchor);
        Formula conjunctionPredicate = Seq(
            Lambda, Sp, x, Comma, Sp,
            Apply("P", x), Sp, Land, Sp, Apply("Q", x));
        Formula conjunction = Apply(
            "robustKnowledge", admissible, evidence,
            Grp(conjunctionPredicate), anchor);
        Formula statePredicate = Arrow(stateType, proposition);
        Formula evidenceMap = Arrow(stateType, evidenceType);
        Formula types = Seq(
            stateType, Comma, Sp, evidenceType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            admissible, Comma, Sp, p, Comma, Sp, q, Colon, Sp,
            statePredicate, Comma, Sp,
            evidence, Colon, Sp, evidenceMap, Comma, Sp,
            anchor, Colon, Sp, stateType);

        return Disp(Seq(
            Forall, Sp, types, Comma, RowBreak, Grp(),
            pKnowledge, Sp, Land, Sp, qKnowledge, Sp, Rightarrow, RowBreak, Grp(),
            conjunction, Dot));
    }
}
