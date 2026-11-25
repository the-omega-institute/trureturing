using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteAnalyticDerivativeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteAnalyticDerivative";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Differential of the raw five-site observation",
        H("Differential of the raw five-site observation"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesiteanalyticderivative-result"),
            DeclarationHandle.Create(Module + ".fderiv_raw_apply"),
            H("Differential of the raw five-site observation"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The real derivative at a rational input agrees with the rational Jacobian acting on the chosen direction."))),
            DescribeRole.Theorem))));
}
