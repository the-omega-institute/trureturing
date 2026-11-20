using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteCompactChartDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteCompactChart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine coordinates on the compact five-site source",
        H("Affine coordinates on the compact five-site source"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesitecompactchart-result"),
            DeclarationHandle.Create(Module + ".affine_round_trip_of_source"),
            H("Affine coordinates on the compact five-site source"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "On the indicated open chart, projector entry ratios reconstruct the affine coordinates and recover the original compact source point."))),
            DescribeRole.Theorem))));
}
