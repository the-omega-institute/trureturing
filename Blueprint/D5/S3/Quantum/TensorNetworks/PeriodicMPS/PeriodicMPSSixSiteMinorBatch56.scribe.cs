using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteMinorBatch56Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site minor values at residues 56 through 63",
        H("Six-site minor values at residues 56 through 63"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteminorbatch56-pointvalues"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch56.pointValues"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Triangular matrix products certify both deleted Jacobian determinants at residues 56 through 63 modulo 1009."))), DescribeRole.Theorem))));
}
