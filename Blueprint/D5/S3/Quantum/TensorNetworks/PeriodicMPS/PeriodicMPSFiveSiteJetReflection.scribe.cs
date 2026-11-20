using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteJetReflectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteJetReflection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact polynomial evaluation of five-site jets",
        H("Exact polynomial evaluation of five-site jets"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitejetreflection-result"),
            DeclarationHandle.Create(Module + ".eval_pathPolynomial_real"),
            H("Exact polynomial evaluation of five-site jets"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Evaluating the rational path polynomials over the reals gives the raw observation along the corresponding quadratic path."))),
            DescribeRole.Theorem))));
}
