using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSFiveSitePhysicalObservationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSitePhysicalObservation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real coordinates for the physical five-site marginal",
        H("Real coordinates for the physical five-site marginal"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitephysicalobservation-result"),
            DeclarationHandle.Create(Module + ".measured_eq_iff"),
            H("Real coordinates for the physical five-site marginal"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "The nine real readout coordinates determine the entire normalized two-site marginal on the compact source."))),
            DescribeRole.Theorem))));
}
