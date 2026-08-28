using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class KnowledgeAlongDependencyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/KnowledgeAlongDependency.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Readout refinement along dependency paths enlarges answerability and shrinks target "
            + "defects.",
        H("Knowledge Along Dependency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("answerability-grows-along-dependency-paths"),
                DeclarationHandle.Create(Prefix + "answerableQuestions_mono_of_reachable"),
                H("Answerable questions grow along dependency paths"),
                StatementSource.FromAuthor(AnswerabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume each dependency edge carries the displayed readout refinement. "
                            + "Along a supplied reflexive-transitive path, questions answerable at "
                            + "the first readout remain answerable at the last.")),
                    Paragraph(Text(
                        "The result is a set inclusion for the two endpoint readouts. It does not "
                            + "assert equality of answerable-question families."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-risk-shrinks-along-dependency-paths"),
                DeclarationHandle.Create(Prefix + "targetRisk_antitone_of_reachable"),
                H("Target risk shrinks along dependency paths"),
                StatementSource.FromAuthor(RiskFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the same refinement-carrying path and a displayed set of target "
                            + "readouts, every risk pair remaining at the last node was already a "
                            + "risk pair at the first.")),
                    Paragraph(Text(
                        "The target set is fixed on both sides of the inclusion; the theorem makes "
                            + "no comparison between different target families."))),
                DescribeRole.Theorem))));

    private static Formula ReadoutType()
    {
        Formula node = F.Id("node");
        return Seq(
            Open, Forall, Sp, node, Colon, Sp, F.Id("Node"), Comma, Sp,
            Call("Concept", F.Id("State"), Call("Coordinate", node)), Close);
    }

    private static Formula CommonPrefix(Formula conclusion)
    {
        Formula edge = F.Id("edge");
        Formula readout = F.Id("readout");
        Formula first = F.Id("first");
        Formula last = F.Id("last");
        Formula hypotheses = Seq(
            Call("EdgeRefines", edge, readout), Sp, Land, Sp,
            Call("ReflTransGen", edge, first, last));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("Coordinate"), Colon, Sp,
            F.Id("Node"), Sp, To, Sp, F.Id("Type"), Comma, Sp,
            edge, Colon, Sp,
            F.Id("Node"), Sp, To, Sp, F.Id("Node"), Sp, To, Sp, F.Id("Prop"),
            Comma, RowBreak, Grp(), readout, Colon, Sp, ReadoutType(), Comma, Sp,
            first, Comma, Sp, last, Colon, Sp, F.Id("Node"), Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot, End, Grp(F.Id("gathered"))));
    }

    private static Formula AnswerabilityFormula() => CommonPrefix(Seq(
        Call("AnswerableQuestions", Call("readout", F.Id("first"))),
        Sp, Subseteq, Sp,
        Call("AnswerableQuestions", Call("readout", F.Id("last")))));

    private static Formula RiskFormula()
    {
        Formula edge = F.Id("edge");
        Formula readout = F.Id("readout");
        Formula first = F.Id("first");
        Formula last = F.Id("last");
        Formula targets = F.Id("targets");
        Formula hypotheses = Seq(
            Call("EdgeRefines", edge, readout), Sp, Land, Sp,
            Call("ReflTransGen", edge, first, last));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("Coordinate"), Colon, Sp,
            F.Id("Node"), Sp, To, Sp, F.Id("Type"), Comma, Sp,
            edge, Colon, Sp,
            F.Id("Node"), Sp, To, Sp, F.Id("Node"), Sp, To, Sp, F.Id("Prop"),
            Comma, RowBreak, Grp(), readout, Colon, Sp, ReadoutType(), Comma, Sp,
            first, Comma, Sp, last, Colon, Sp, F.Id("Node"), Comma, Sp,
            targets, Colon, Sp,
            Call("Set", Call("Concept", F.Id("State"), F.Id("Target"))),
            Comma, RowBreak, Grp(), Open, hypotheses, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Call("targetRisk", Call("readout", last), targets), Sp, Subseteq, Sp,
            Call("targetRisk", Call("readout", first), targets), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
