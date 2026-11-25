using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class ProjectionSpectralTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rectangular spectra and projection frames",
        H("Rectangular spectra and projection frames"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-sum-mul-reverse"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport.spectralSum_mul_reverse"),
                H("Spectral sums of rectangular products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let A and B be rectangular complex matrices with Hermitian products AB and BA. Summing any real function that vanishes at zero over the two spectra gives the same value. The rectangular characteristic polynomial identity accounts for the extra zero roots."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-projection-frame"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/ProjectionSpectralTransport.exists_projection_frame"),
                H("An isometric frame of the prescribed rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every Hermitian idempotent Q of rank d is VV† for a matrix V with d columns and V†V = I. The zero and identity projections give the empty and reindexed identity frames. A complementary frame supplies the intermediate case."))),
                DescribeRole.Theorem))));
}
