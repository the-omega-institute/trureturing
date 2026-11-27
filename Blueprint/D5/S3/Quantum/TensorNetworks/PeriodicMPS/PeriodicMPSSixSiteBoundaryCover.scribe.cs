using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteBoundaryCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-dimensional cover of the compact boundary",
        H("Six-dimensional cover of the compact boundary"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteboundarycover-real-boundary-observation-cover"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteBoundaryCover.real_boundary_observation_cover"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The traceless plane and the projectivized exceptional normal directions give a finite family of differentiable observation images from six real coordinates."))), DescribeRole.Theorem))));
}
