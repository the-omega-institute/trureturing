using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class CanonicalCompletionIdempotenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Predictive completion is canonically idempotent.",
        H("Canonical Completion Idempotence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-completion-idempotence"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/CanonicalCompletionIdempotence."
                        + "canonical_completion_idempotence"),
                H("The second completion is canonically equivalent to the first"),
                StatementSource.FromAuthor(IdempotenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A predictive completion is the quotient by equality of every future "
                            + "readout value, with its update and current readout induced from "
                            + "the source dynamics.")),
                    Paragraph(Text(
                        "Completing that induced readout a second time produces the second-stage "
                            + "future relation. The existing cascade-completion construction "
                            + "supplies its canonical equivalence with the direct completion.")),
                    Paragraph(Text(
                        "The Lean declaration exposes that equivalence itself, rather than only "
                            + "an inhabitation claim, by applying the repository's exact "
                            + "cascadeCompletionEquiv theorem with the identity forgetting map.")),
                    Paragraph(Text(
                        "Repository search found the exact canonical declaration "
                            + "cascadeCompletionEquiv; it is imported and applied directly."))),
                DescribeRole.Definition))));

    private static Formula IdempotenceFormula()
    {
        Formula q = F.Id("q");
        Formula completed = Call("C", q);
        Formula second = Call("C", completed);

        return Disp(Seq(second, Sp, Equiv, Sp, completed, Dot));
    }
}
