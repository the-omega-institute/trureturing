using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSitePhysicalRankAssemblyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankAssembly";
    private const string Title = "A nonvanishing slice minor gives full rank of the graph readout";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitephysicalrankassembly-result"),
            DeclarationHandle.Create(Module + ".injective_fderiv_graphReadout"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("At an ordinary seven-site chart point, assume its aligned mixed coordinate is nonzero. If a selected critical minor evaluated on the corresponding real slice is nonzero, the real derivative of the nine-component graph readout is injective.")),
                Paragraph(Text("The slice calculation relates the five coordinate columns, three rotation columns and radial column of the raw rows to the differential of the normalized marginal. The rank criterion is transported from the aligned slice to the original ordinary point."))),
            DescribeRole.Theorem))));
}
