using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteSpecialGermsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two local charts over the six-site special observation",
        H("The two local charts over the six-site special observation"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitespecialgerms-specialpoint-exhausts"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialGerms.specialPoint_exhausts"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Both certified raw chart centers represent the two points of the complete compact special fiber."))), DescribeRole.Theorem))));
}
