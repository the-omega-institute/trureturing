using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteMinorBatch8Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site minor values at residues 8 through 15",
        H("Six-site minor values at residues 8 through 15"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteminorbatch8-pointvalues"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch8.pointValues"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Triangular matrix products certify both deleted Jacobian determinants at residues 8 through 15 modulo 1009."))), DescribeRole.Theorem))));
}
