using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class UnequalGeometryEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pinching gain in unequal fibers",
        H("The pinching gain in unequal fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gain-eq-unequal-row-effects"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/UnequalGeometryEntropy.gain_eq_unequal_rowEffects"),
                H("Spectral evaluation on a physical input"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(
                    Paragraph(Text("For an input P/r expressed through a frame V, the pinched projection decomposes into its fiber compressions. These blocks are V_jV_j† or their complements. Rectangular spectral transport compares them with V_j†V_j. Preservation of trace cancels the scaling terms involving log r, leaving the direct or reflected spectral sum divided by the original rank r."))),
                DescribeRole.Theorem))));
}
