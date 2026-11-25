using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteProjectiveLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full-degree interpolation for the six-site minors",
        H("Full-degree interpolation for the six-site minors"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteprojectiveline-integral-certificate-of-point-values"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteProjectiveLine.integral_certificate_of_point_values"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Finite-field interpolation identifies both residual line polynomials and certifies a nonzero integral resultant."))), DescribeRole.Theorem))));
}
