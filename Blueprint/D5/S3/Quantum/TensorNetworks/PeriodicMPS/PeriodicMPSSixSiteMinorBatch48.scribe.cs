using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteMinorBatch48Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-site minor values at residues 48 through 55",
        H("Six-site minor values at residues 48 through 55"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteminorbatch48-pointvalues"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteMinorBatch48.pointValues"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Triangular matrix products certify both deleted Jacobian determinants at residues 48 through 55 modulo 1009."))), DescribeRole.Theorem))));
}
