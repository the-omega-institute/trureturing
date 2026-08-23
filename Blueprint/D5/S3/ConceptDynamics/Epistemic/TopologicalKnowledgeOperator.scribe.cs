using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class TopologicalKnowledgeOperatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Topological interior satisfies the four knowledge-operator laws.",
        H("Topological Knowledge Operator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("topological-knowledge-operator-laws"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Epistemic/TopologicalKnowledgeOperator."
                        + "topological_knowledge_operator_laws"),
                H("Interior is a topological knowledge operator"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("X"), Colon, Sp, Operatorname,
                    Grp(F.Id("Type")), Comma, RowBreak, Grp(),
                    Operatorname, Grp(F.Id("TopologicalSpace")),
                    Open, F.Id("X"), Close, Sp, Rightarrow, RowBreak, Grp(),
                    Open,
                    Forall, Sp, F.Id("P"), Colon, Sp,
                    Operatorname, Grp(F.Id("Set")), Open, F.Id("X"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("interior")), Open, F.Id("P"), Close,
                    Sp, Subseteq, Sp, F.Id("P"),
                    Close, Sp, Land, RowBreak, Grp(),
                    Open,
                    Forall, Sp, F.Id("P"), Comma, Sp, F.Id("Q"), Colon, Sp,
                    Operatorname, Grp(F.Id("Set")), Open, F.Id("X"), Close,
                    Comma, Sp, F.Id("P"), Sp, Subseteq, Sp, F.Id("Q"), Sp,
                    Rightarrow, Sp,
                    Operatorname, Grp(F.Id("interior")), Open, F.Id("P"), Close,
                    Sp, Subseteq, Sp,
                    Operatorname, Grp(F.Id("interior")), Open, F.Id("Q"), Close,
                    Close, Sp, Land, RowBreak, Grp(),
                    Open,
                    Forall, Sp, F.Id("P"), Comma, Sp, F.Id("Q"), Colon, Sp,
                    Operatorname, Grp(F.Id("Set")), Open, F.Id("X"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("interior")), Open,
                    Operatorname, Grp(F.Id("intersection")), Open,
                    F.Id("P"), Comma, Sp, F.Id("Q"), Close, Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("intersection")), Open,
                    Operatorname, Grp(F.Id("interior")), Open, F.Id("P"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("interior")), Open, F.Id("Q"), Close,
                    Close,
                    Close, Sp, Land, RowBreak, Grp(),
                    Open,
                    Forall, Sp, F.Id("P"), Colon, Sp,
                    Operatorname, Grp(F.Id("Set")), Open, F.Id("X"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("interior")), Open,
                    Operatorname, Grp(F.Id("interior")), Open, F.Id("P"), Close,
                    Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("interior")), Open, F.Id("P"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The knowledge operator is the canonical interior operation of the "
                            + "given topology; it is not defined from any target law.")),
                    Paragraph(Text(
                        "The public statement separately exposes factivity, monotonicity, "
                            + "finite-intersection preservation, and positive introspection.")),
                    Paragraph(Text(
                        "Each conjunct directly applies the corresponding pinned library law "
                            + "for topological interior."))),
                DescribeRole.Theorem))));
}
