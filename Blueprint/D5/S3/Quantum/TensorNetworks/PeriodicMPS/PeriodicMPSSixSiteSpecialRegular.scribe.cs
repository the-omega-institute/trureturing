using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSiteSpecialRegularDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective normalized differential at the six-site special lifts",
        H("Injective normalized differential at the six-site special lifts"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitespecialregular-injective-normalizedobservation-special"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteSpecialRegular.injective_normalizedObservation_special"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Holding the independently varied raw trace fixed transports the invertible tangent Jacobian to the trace-one chart."))), DescribeRole.Theorem))));
}
