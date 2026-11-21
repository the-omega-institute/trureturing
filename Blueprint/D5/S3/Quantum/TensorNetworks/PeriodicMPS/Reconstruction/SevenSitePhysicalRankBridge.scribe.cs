using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSitePhysicalRankBridgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankBridge";
    private const string Title = "Differentiable covers of the seven-site physical critical slice";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitephysicalrankbridge-result"),
            DeclarationHandle.Create(Module + ".cover_physicalChart_criticalSlice"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The ordinary-coordinate image of the certified critical slice through the two phase charts is contained in a countable union of differentiable images from six real coordinates. The domains combine three rotation coordinates with the three coordinates of the differentiable slice cover.")),
                Paragraph(Text("The phase charts restore the mixed coordinate and the remaining ordinary coordinates. Their real analyticity lets each of the two charts carry the slice cover into the original ordinary coordinates."))),
            DescribeRole.Theorem))));
}
