using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteGraphBoundaryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphBoundary";
    private const string Title = "Hausdorff dimension of the compact seven-site graph boundary";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitegraphboundary-result"),
            DeclarationHandle.Create(Module + ".dimH_boundary_le"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The complement of the ordinary chart in the compact seven-site trace graph has real Hausdorff dimension at most six. The graph boundary admits a differentiable cover that includes the traceless and proportional amplitude-zero limits, together with the chart obtained by exchanging the binary labels.")),
                Paragraph(Text("The cover is constructed on open domains in three complex coordinates. The same dimension bound holds for the boundary as a subset of the compact graph subtype."))),
            DescribeRole.Theorem))));
}
