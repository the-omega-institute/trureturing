using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformGraphBoundaryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphBoundary";
    private const string Title = "Hausdorff dimension of the uniform compact graph boundary";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformgraphboundary-result"),
            DeclarationHandle.Create(Module + ".dimH_chartBoundary_le"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("At every period n ≥ 2 the complement of the ordinary trace-one chart in the compact graph has real Hausdorff dimension at most six. Differentiable charts cover the traceless and proportional limits and the points obtained by exchanging the binary labels."))),
            DescribeRole.Theorem))));
}
