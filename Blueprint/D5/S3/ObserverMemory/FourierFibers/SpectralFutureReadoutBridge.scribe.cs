using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class SpectralFutureReadoutBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite spectral time-delay word is the canonical Trueturning future-readout word for diagonal evolution.",
        H("Spectral Future-Readout Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("future-readout-word-eq-crystal-time-word"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/SpectralFutureReadoutBridge.future_readout_word_eq_crystal_time_word"),
                H("Spectral delays reuse the canonical future word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For one-step diagonal spectral evolution and the modal-sum sensor, the repository's canonical finite future-readout word equals the finite crystal time word coordinatewise.")),
                    Paragraph(Text(
                        "This bridge prevents a second delay-coordinate API and connects finite Koopman-style time-delay reasoning to the existing observer-completion machinery."))),
                DescribeRole.Theorem))));
}
