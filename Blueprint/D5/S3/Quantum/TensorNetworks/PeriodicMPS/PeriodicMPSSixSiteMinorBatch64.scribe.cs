using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteMinorBatch64Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site minor values at residues 64 through 71",
        H("Six-site minor values at residues 64 through 71"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteminorbatch64-pointvalues"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch64.pointValues"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Triangular matrix products certify both deleted Jacobian determinants at residues 64 through 71 modulo 1009."))), DescribeRole.Theorem))));
}
