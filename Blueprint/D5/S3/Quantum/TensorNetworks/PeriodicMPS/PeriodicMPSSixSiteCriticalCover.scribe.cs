using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteCriticalCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-dimensional cover of the six-site critical equations",
        H("Six-dimensional cover of the six-site critical equations"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitecriticalcover-cover-critical-equations"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteCriticalCover.cover_critical_equations"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The conjugate slice of the simultaneous minor zeros lies in countably many differentiable images of six-dimensional real domains."))), DescribeRole.Theorem))));
}
