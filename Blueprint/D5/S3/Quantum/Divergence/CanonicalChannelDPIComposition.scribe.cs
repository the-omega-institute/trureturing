using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CanonicalChannelDPICompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Support-aware quantum relative entropy contracts along a composite finite channel.",
        H("Composite Quantum Channel Data Processing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("composite-channel-relative-entropy-dpi"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/CanonicalChannelDPIComposition."
                        + "extended_quantum_relative_entropy_comp_dpi"),
                H("Data processing is closed under sequential composition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Apply the existing support-aware data-processing theorem to the "
                            + "second channel on the intermediate state pair, then to the "
                            + "first channel on the original pair. QuantumChannel.comp_mapState "
                            + "identifies the composite action with sequential state evolution.")),
                    Paragraph(Text(
                        "The three finite carriers may live in independent universes. "
                            + "Singular states remain covered by the existing WithTop-valued "
                            + "support-aware relative entropy."))),
                DescribeRole.Theorem))));
}
