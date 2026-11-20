using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteEliminationCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six polynomial consequences of the six-site special equations",
        H("Six polynomial consequences of the six-site special equations"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteeliminationcertificate-columns-zero"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteEliminationCertificate.columns_zero"),
            H("Vanishing of the six certificate columns"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Substituting the projection into the three invariant equations gives the vacuum, exchange, and coherence polynomials. Each of the six columns is an exact polynomial combination of these equations, in the row basis u v², v², u v, v, u, 1. Their simultaneous vanishing supplies the six equalities used in the cofactor elimination."))),
            DescribeRole.Theorem))));
}
