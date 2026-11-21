using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteJetReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient transport for the six-site quadratic paths",
        H("Coefficient transport for the six-site quadratic paths"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitejetreflection-cubiccoefficient-eq-coeff"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteJetReflection.cubicCoefficient_eq_coeff"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The third mixed component of the iterated dual-number evaluation gives the cubic coefficient of the rational path polynomial."))), DescribeRole.Theorem))));
}
