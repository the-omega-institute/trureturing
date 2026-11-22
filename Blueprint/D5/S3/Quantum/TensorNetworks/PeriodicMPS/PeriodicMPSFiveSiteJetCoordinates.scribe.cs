using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSiteJetCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteJetCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw observation and its Taylor coefficients",
        H("Raw observation and its Taylor coefficients"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitejetcoordinates-result"),
            DeclarationHandle.Create(Module + ".cubicCoefficient"),
            H("Raw observation and its Taylor coefficients"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The polynomial observation in nine real coordinates gives the rational cubic coefficient along a quadratic path."))),
            DescribeRole.Definition))));
}
