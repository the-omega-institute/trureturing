using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9PositivePairedKernelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive kernels on occupied fibre components",
        H("Positive kernels on occupied fibre components"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-kernel-absolute-value"),
                DeclarationHandle.Create(Module + ".abs_mem_kernel"),
                H("Absolute values preserve a complementary Gram kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the occupied matrix is entrywise nonnegative and its Gram plus the empty Gram is scalar, replacing a kernel vector by its absolute value preserves the kernel. This follows from the fixed squared norm and the increased occupied quadratic form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("paired-kernel-per-weight-block"),
                DeclarationHandle.Create(Module + ".exists_fixed_occupiedComponent_emptyFibre_kernel"),
                H("One occupied component works for every weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The occupied graph decomposes the complementary Gram into blocks. Polynomial determinant factorization selects a single universally singular block. For positive transverse weights the kernel can be chosen with the switching signs, and every coefficient on that block is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("paired-kernel-actual-two-blocks"),
                DeclarationHandle.Create(Module + ".exists_two_components_with_fixed_occupied_kernel"),
                H("Two actual components with fixed kernel blocks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The universal weighted singularity of two actual components forces each dominant axis to have a fixed occupied block carrying a boundary kernel for every real weighting. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance"))]));
}
