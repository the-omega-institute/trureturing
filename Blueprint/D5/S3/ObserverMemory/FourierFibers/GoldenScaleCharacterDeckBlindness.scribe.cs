using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class GoldenScaleCharacterDeckBlindnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer golden Fourier characters forget complete deck depth while the golden helix retains it.",
        H("Golden Scale Character Deck Blindness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-helix-fourier-readout-not-injective"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/GoldenScaleCharacterDeckBlindness.golden_helix_fourier_readout_not_injective"),
                H("Quotient Fourier readout forgets the helix sheet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "One full golden scale period leaves every integer Fourier character unchanged, although the universal-cover helix level increases.")),
                    Paragraph(Text(
                        "The theorem reuses GoldenScaleHelix to separate quotient phase from completion-depth memory. Adding the level coordinate detects the deck step."))),
                DescribeRole.Theorem))));
}
