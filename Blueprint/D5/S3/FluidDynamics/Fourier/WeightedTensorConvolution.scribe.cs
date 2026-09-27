using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class WeightedTensorConvolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/WeightedTensorConvolution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic weighted tensor convolution on the integer lattice has norm bound sixteen.",
        H("Weighted Tensor Convolution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-tensor-convolution-weight"),
                DeclarationHandle.Create(Prefix + "weight"),
                H("weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quadratic Fourier weight on the two-dimensional integer lattice."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-tensor-convolution-outer"),
                DeclarationHandle.Create(Prefix + "outer"),
                H("outer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex outer product uses the Euclidean tensor fibre, hence the Frobenius norm."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-tensor-convolution-convolution"),
                DeclarationHandle.Create(Prefix + "convolution"),
                H("convolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient convolution sums over every lattice frequency."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-tensor-convolution-weighted-tensor-convolution"),
                DeclarationHandle.Create(Prefix + "weighted_tensor_convolution"),
                H("weighted tensor convolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary complex vector coefficients with summable quadratic weighted energies, each tensor convolution converges absolutely, its weighted energy is summable, and the square root of that energy is at most sixteen times the product of the two input energy square roots."))),
                DescribeRole.Theorem))));
}
