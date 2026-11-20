using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteLineBezoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bézout identity for the six-site minors modulo 1009",
        H("Bézout identity for the six-site minors modulo 1009"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitelinebezout-coprime-line-restrictions"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteLineBezout.coprime_line_restrictions"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The convolution identities verify a polynomial Bézout identity over the residue field."))), DescribeRole.Theorem))));
}
