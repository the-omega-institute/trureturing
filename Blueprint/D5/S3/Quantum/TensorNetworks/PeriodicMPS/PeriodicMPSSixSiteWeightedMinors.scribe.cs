using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteWeightedMinorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree of the six-site weighted critical minors",
        H("Degree of the six-site weighted critical minors"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteweightedminors-symbolicminor-weight"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteWeightedMinors.symbolicMinor_weight"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Each selected nine-by-nine Jacobian cofactor has weighted degree 93 before restriction to the fixed line."))), DescribeRole.Theorem))));
}
