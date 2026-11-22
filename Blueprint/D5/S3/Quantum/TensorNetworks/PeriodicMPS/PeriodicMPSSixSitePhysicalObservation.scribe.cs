using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSSixSitePhysicalObservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace normalization in the raw six-site chart",
        H("Trace normalization in the raw six-site chart"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpssixsitephysicalobservation-normalize-raw-eq-observation"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSitePhysicalObservation.normalize_raw_eq_observation"),
            H("Proof"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Dividing the raw readout by its trace agrees with the normalized adjacent density in the compact source."))), DescribeRole.Theorem))));
}
