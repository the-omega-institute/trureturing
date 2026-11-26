using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteActualSourceChartDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteActualSourceChart";
    private const string Title = "An actual-state chart at the seven-site hard-core projector";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensiteactualsourcechart-result"),
            DeclarationHandle.Create(Module + ".exists_witness_chart"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("An open chart around the seven-site hard-core projector in the compact state source has a Lipschitz inverse. The normalized trace-word projector gives the chart map and the literal projector decoder gives its inverse. The target consists entirely of actual periodic binary bond-two projectors.")),
                Paragraph(Text("An open guard on the adjacent two-site observation confines nearby competitors to actual states. The vacuum entry stays nonzero near the center and permits recovery of the ordinary trace coordinates."))),
            DescribeRole.Theorem))));
}
