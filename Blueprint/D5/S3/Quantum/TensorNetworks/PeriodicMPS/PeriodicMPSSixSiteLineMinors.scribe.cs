using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteLineMinorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient transport for the six-site line minors",
        H("Coefficient transport for the six-site line minors"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitelineminors-map-minor"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteLineMinors.map_minor"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The six-site Gram Jacobian is computed by square-zero perturbations, and the line minors commute with coefficient homomorphisms."))), DescribeRole.Theorem))));
}
