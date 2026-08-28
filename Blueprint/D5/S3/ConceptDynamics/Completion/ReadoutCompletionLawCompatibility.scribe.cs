using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Completion;

internal sealed class ReadoutCompletionLawCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var mass = Id("mass");
        var readout = Id("readout");
        var target = Id("target");
        var equality = Equal(
            Call("readoutTargetLaw", mass, readout, target),
            Call("completionLaw", mass, readout, target));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The communication and completion modules use the same joint pushforward law.",
            H("Readout and Completion Law Compatibility"),
            Blocks(
                Paragraph(Text(
                    "For every finite source type, real-valued mass, readout, and target, "
                        + "the readout-target law is equal as a function to the completion "
                        + "law. The communication-side Concept type is definitionally the "
                        + "same function type used by the completion-side declaration.")),
                Paragraph(Text(
                    "This identification does not make an arbitrary real-valued mass a "
                        + "probability law: normalization and nonnegativity are not part of "
                        + "either constructor. It also does not identify the surrounding "
                        + "monotonicity and information-cost theorems, which have different "
                        + "inputs and conclusions.")),
                Describe.Lean(
                    DescribeId.Create("readout-target-law-is-the-completion-law"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/Completion/"
                            + "ReadoutCompletionLawCompatibility."
                            + "readoutTargetLaw_eq_completionLaw"),
                    H("The readout-target law is the completion law"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(equality)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Unfolding the two declarations and the Concept function carrier "
                            + "leaves the same paired pushforward on both sides."))),
                    DescribeRole.Theorem))));
    }
}
