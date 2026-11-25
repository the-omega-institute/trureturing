using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteCriticalCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact coprimality of the six-site line restrictions",
        H("Exact coprimality of the six-site line restrictions"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitecriticalcertificate-coprime-restrictions"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalCertificate.coprime_restrictions"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Ninety-four residue evaluations and the modular Bézout identity imply coprimality of the characteristic-zero degree-93 restrictions."))), DescribeRole.Theorem))));
}
