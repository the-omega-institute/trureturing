using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformCommonSpectralRankTransportDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralRankTransport";
    private const string Title = "Rank of the projective Gram derivative";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformcommonspectralranktransport-projectivegramdifferential-rank-eq-eight"),
                DeclarationHandle.Create(Module + ".projectiveGramDifferential_rank_eq_eight"),
                H("Rank of the projective Gram derivative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace-word Jacobian and radial direction give rank eight for the projective derivative."))),
                DescribeRole.Theorem))));
}
