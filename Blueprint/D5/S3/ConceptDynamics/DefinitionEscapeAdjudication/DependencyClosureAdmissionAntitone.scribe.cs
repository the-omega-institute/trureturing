using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class DependencyClosureAdmissionAntitoneDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/"
            + "DependencyClosureAdmissionAntitone."
            + "dependency_closure_admission_antitone";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expanding a frozen commitment's dependency closure can only remove "
            + "admissible adjudication evidence.",
        H("Dependency-Closure Admission Antitonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dependency-closure-admission-antitone"),
                DeclarationHandle.Create(Declaration),
                H("Adjudication admission is antitone in the dependency closure"),
                StatementSource.FromAuthor(AdmissionAntitoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The context fixes the event, round, and time prefix of the role ledger, "
                            + "the after-freeze first-seen condition, and provenance reachability. "
                            + "AdmissibleJudge requires an Adjudicate event and rejects both a "
                            + "record that reaches the closure and an adaptive Generate, Tune, or "
                            + "Select event whose dependencies touch it.")),
                    Paragraph(Text(
                        "If the old closure is contained in the new closure, every old direct "
                            + "reachability witness and every old adaptive-use touch witness is "
                            + "also a witness for the new closure. Negating those two conditions "
                            + "therefore reverses the inclusion at the admission predicate.")),
                    Paragraph(Text(
                        "This formalizes the dependency-pollution antitonicity clause of Part 48.3 "
                            + "in definition-escape-completion-theory atom "
                            + "generic-residual-661d307df0f3cf908d1089852a0092a99bdea5a95b4148987313a2d4df5e016b. "
                            + "The append-only ledger invariance and set-level contamination "
                            + "clauses remain separate claims."))),
                DescribeRole.Theorem))));

    private static Formula SetOf(Formula carrier) => Call("Set", carrier);

    private static Formula AdmissionAntitoneFormula()
    {
        Formula evidence = F.Id("Evidence");
        Formula artifact = F.Id("Artifact");
        Formula context = F.Id("context");
        Formula oldClosure = F.Id("oldClosure");
        Formula newClosure = F.Id("newClosure");
        Formula record = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula admissionContext = Call("AdmissionContext", evidence, artifact);

        Formula Admissible(Formula closure) =>
            Call("AdmissibleJudge", context, closure, record);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, evidence, Comma, Sp, artifact, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            context, Colon, Sp, admissionContext, Comma, RowBreak, Grp(),
            oldClosure, Comma, Sp, newClosure, Colon, Sp, SetOf(artifact),
            Comma, RowBreak, Grp(),
            oldClosure, Sp, Subseteq, Sp, newClosure, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, record, Colon, Sp, evidence, Comma, Sp,
            Admissible(newClosure), Sp, Rightarrow, Sp,
            Admissible(oldClosure), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
