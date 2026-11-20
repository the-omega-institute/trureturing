using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteCriticalChartDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprime six-site minors in the affine trace chart",
        H("Coprime six-site minors in the affine trace chart"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitecriticalchart-relatively-prime-chartminors"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalChart.relatively_prime_chartMinors"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The two weighted homogeneous minors remain relatively prime after dehomogenizing the forward and reverse trace coordinates."))), DescribeRole.Theorem))));
}
