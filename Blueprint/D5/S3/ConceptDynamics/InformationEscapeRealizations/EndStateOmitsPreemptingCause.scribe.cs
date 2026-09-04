using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class EndStateOmitsPreemptingCauseDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint and active-cause readouts realize the five-class preemption kernel.",
        H("End State Omits Preempting Cause Realization"),
        Blocks(
            Node("end-state-preemption-realization",
                "end_state_omits_preempting_cause_realization",
                "Preemption realization equivalence",
                Call("LegacyPrimitiveRealization", F.Id("endStateOmitsPreemptingCauseArena"),
                    F.Id("EndStateOmitsPreemptingCauseStatement"),
                    F.Id("endStateOmitsPreemptingCauseRealization")),
                "Both directions encode or decode the ordered-preemption facts and preserve the object-bound factorization clause."),
            Node("end-state-preemption-partition-count",
                "end_state_omits_preempting_cause_partition_count",
                "Five kernel classes", Seq(Call("card", F.Id("signatureClasses")),
                    Sp, Eq, Sp, D(5)),
                "Kernel evaluation groups the nine traces into the five census classes."),
            Node("end-state-preemption-private-pair",
                "end_state_omits_preempting_cause_private_pair",
                "Private trace separation",
                Call("Not", Call("agrees", F.Id("endStateOmitsPreemptingCauseRealization"),
                    F.Id("aThenB"), F.Id("bThenA"))),
                "The compiled bundle separates AB from BA through cause, admission, and anchor content."))));

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(statement, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);
}
