using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class RobustKnowledgeRefinementMonotonicityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Robust knowledge is monotone under evidence refinement.",
        H("Robust Knowledge Refinement Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robust-knowledge-monotone-under-refinement"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Epistemic/RobustKnowledgeRefinementMonotonicity."
                        + "robust_knowledge_monotone_under_refinement"),
                H("Evidence refinement preserves robust knowledge"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The admissibility predicate, coarse and refined evidence channels, "
                            + "proposition, and anchor are independent source primitives.")),
                    Paragraph(Text(
                        "Refinement is the canonical factorization order: the coarse evidence "
                            + "channel factors through the refined channel. Robust knowledge is "
                            + "the established predicate requiring truth at the admissible anchor "
                            + "and throughout its admissible evidence fiber.")),
                    Paragraph(Text(
                        "Equality of refined evidence values remains equality after the public "
                            + "factor map. Every refined anchor fiber is therefore contained in "
                            + "the coarse anchor fiber, where the proposition is already true.")),
                    Paragraph(Text(
                        "Repository searches found the exact family primitives but no existing "
                            + "theorem combining them. Pinned Mathlib has generic factorization "
                            + "lemmas but no admissible anchored knowledge result."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula coarseType = F.Id("B");
        Formula refinedType = Seq(F.Id("B"), Apos);
        Formula admissible = F.Id("Adm");
        Formula coarseEvidence = F.Id("E");
        Formula refinedEvidence = Seq(F.Id("E"), Apos);
        Formula predicate = F.Id("P");
        Formula anchor = F.Id("a");
        Formula proposition = F.Id("Prop");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula sourceKnowledge = Call(
            "robustKnowledge", admissible, coarseEvidence, predicate, anchor);
        Formula refinedKnowledge = Call(
            "robustKnowledge", admissible, refinedEvidence, predicate, anchor);

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, coarseType, Comma, Sp, refinedType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            admissible, Comma, Sp, predicate, Colon, Sp,
            Arrow(stateType, proposition), Comma, Sp,
            coarseEvidence, Colon, Sp, Arrow(stateType, coarseType), Comma, Sp,
            refinedEvidence, Colon, Sp, Arrow(stateType, refinedType), Comma, Sp,
            anchor, Colon, Sp, stateType, Comma, RowBreak, Grp(),
            Call("Refines", coarseEvidence, refinedEvidence), Sp, Land, Sp,
            sourceKnowledge, Sp, Rightarrow, RowBreak, Grp(),
            refinedKnowledge, Dot));
    }
}
