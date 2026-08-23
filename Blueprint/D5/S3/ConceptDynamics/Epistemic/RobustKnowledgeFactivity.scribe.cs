using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class RobustKnowledgeFactivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Robust knowledge entails truth at its evidence anchor.",
        H("Robust Knowledge Factivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robust-knowledge-factivity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeFactivity."
                        + "robust_knowledge_factivity"),
                H("Knowledge is factual"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let admissibility and the evidence channel be independent source "
                            + "primitives on an arbitrary state type, and let P be an arbitrary "
                            + "state predicate with anchor a.")),
                    Paragraph(Text(
                        "If P is robustly known at a, then P holds at a. The imported robust "
                            + "knowledge predicate also records admissibility and stability over "
                            + "the entire evidence fiber, so the implication exposes its factual "
                            + "anchor clause without redefining knowledge."))),
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
        Formula predicate = F.Id("P");
        Formula anchor = F.Id("a");
        Formula statePredicate = Arrow(stateType, proposition);
        Formula evidenceMap = Arrow(stateType, evidenceType);
        Formula knowledge = Apply(
            "robustKnowledge", admissible, evidence, predicate, anchor);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, evidenceType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            admissible, Comma, Sp, predicate, Colon, Sp, statePredicate, Comma, Sp,
            evidence, Colon, Sp, evidenceMap, Comma, Sp,
            anchor, Colon, Sp, stateType, Comma, RowBreak, Grp(),
            knowledge, Sp, Rightarrow, Sp, Apply("P", anchor), Dot));
    }
}
