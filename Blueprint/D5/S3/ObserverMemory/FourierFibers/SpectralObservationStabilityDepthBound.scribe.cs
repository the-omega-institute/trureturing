using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class SpectralObservationStabilityDepthBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated finite diagonal modes stabilize the canonical observation relation by the last Vandermonde sample.",
        H("Spectral Observation Stability-Depth Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-observation-stability-depth-le"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/SpectralObservationStabilityDepthBound.spectral_observation_stability_depth_le"),
                H("Finite mode separation bounds canonical stability depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For depth plus one pairwise distinct modes, the canonical future word through that depth is injective and its observation relation has already stabilized.")),
                    Paragraph(Text(
                        "The theorem reuses observationStabilityDepth, futureReadoutWord, and finite Vandermonde tomography rather than defining a second temporal depth."))),
                DescribeRole.Theorem))));
}
