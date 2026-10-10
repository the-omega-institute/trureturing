using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.HiguchiSudbery;

internal sealed class EntropyReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Summing the cubic majorant reduces entropy to the second and third spectral moments. Newton’s identity replaces the third moment by purity and the third elementary symmetric polynomial.",
        H("EntropyReduction"),
        Blocks(Paragraph(Text("The Lean objects in this component are dotProduct v v, C, entropy_spectral_bound, entropy_three_spectra.")))));
}
