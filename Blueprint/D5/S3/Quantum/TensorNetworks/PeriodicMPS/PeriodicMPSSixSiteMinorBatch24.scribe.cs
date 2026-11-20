using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteMinorBatch24Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site minor values at residues 24 through 31",
        H("Six-site minor values at residues 24 through 31"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteminorbatch24-pointvalues"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch24.pointValues"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Triangular matrix products certify both deleted Jacobian determinants at residues 24 through 31 modulo 1009."))), DescribeRole.Theorem))));
}
