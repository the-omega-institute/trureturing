using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class CompressionSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral compression inequality",
        H("Spectral compression inequality"),
        Blocks(Describe.Lean(
            DescribeId.Create("eigenvalue-compression-le"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/CompressionSpectrum.eigenvalue_compression_le"),
            H("Spectral compression inequality"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Isometric compression cannot increase the ordered eigenvalues. The comparison follows by pulling positive spectral subspaces back through the isometry."))),
            DescribeRole.Theorem))));
}
