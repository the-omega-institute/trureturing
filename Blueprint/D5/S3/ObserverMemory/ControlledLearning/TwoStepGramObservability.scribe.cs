using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ControlledLearning;

internal sealed class TwoStepGramObservabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-step controlled experiment removes the scalar ambiguity of all one-step Gram outputs.",
        H("Two-step Gram observability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-step-and-cross-probe-determine-gram"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ControlledLearning/TwoStepGramObservability."
                    + "one_step_and_cross_probe_determine_gram"),
                H("Identify both Gram blocks from reset outputs and a cross probe"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the input and output index types be finite and nonempty. "
                        + "Two pairs of real square Gram blocks share the same rectangular "
                        + "current output W. Fix nonzero step sizes eta and tau and controls "
                        + "G,H. Assume a specified entry of H G-transpose G minus G G-transpose H "
                        + "is nonzero. If every reset one-step output at eta agrees and the "
                        + "two-step output for G followed by H agrees, both Gram blocks agree.")),
                    Paragraph(Text(
                        "The proof first tests the whole one-step family on matrix units. "
                        + "This forces the input-block difference to be c times the identity "
                        + "and the output-block difference to be minus c times the identity. "
                        + "Transport through the actual first-step recurrences leaves zero "
                        + "output difference but changes the two diagonal blocks. The second "
                        + "output difference is exactly c eta-squared tau times the chosen "
                        + "rectangular Gram commutator. Its nonzero entry forces c to vanish.")),
                    Paragraph(Text(
                        "The nonzero premise concerns known probe controls, not a hidden "
                        + "coupling or eigenvalue. The declaration is an algebraic theorem "
                        + "for the displayed recurrences. Positive factor realizations, "
                        + "coordinate-probe construction, the scalar exception, noise bounds, "
                        + "continuous-time comparison and the quantum instrument interpretation "
                        + "are separate ordinary arguments, not claims of this Lean declaration."))),
                DescribeRole.Theorem)),
        []));
}
