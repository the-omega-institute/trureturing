using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteAnalyticDerivativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real derivatives of the six-site jet",
        H("Real derivatives of the six-site jet"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsiteanalyticderivative-fderiv-raw-apply"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteAnalyticDerivative.fderiv_raw_apply"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The rational Jacobian acts as the Fréchet derivative on each real direction at a rational chart point."))), DescribeRole.Theorem))));
}
