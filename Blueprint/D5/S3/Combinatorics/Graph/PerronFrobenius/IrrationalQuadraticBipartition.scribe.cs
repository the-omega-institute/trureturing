using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PerronFrobenius;

internal sealed class IrrationalQuadraticBipartitionDocument : IScribeDocumentDefinition
{
    private const string Graph = "D5/S3/Combinatorics/Graph/PerronFrobenius/";
    private const string Owner = Graph + "IrrationalQuadraticBipartition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bipartition at an irrational Perron value with rational square",
        H("The bipartition under weight-preserving symmetries"),
        Blocks(Describe.Lean(
            DescribeId.Create("quadratic-perron-bipartition"),
            DeclarationHandle.Create(Owner + "preserves_bipartition_of_sq_rat"),
            H("A weight-preserving permutation preserves each color class"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let a finite bipartite graph have symmetric nonnegative rational weights and be connected through its positive-weight edges. Suppose a strictly positive vector has eigenvalue ρ, where ρ is irrational and ρ² is rational. Every permutation preserving the weight matrix preserves the two color classes.")),
                Paragraph(Text("The permutation fixes the positive vector by the maximum ratio argument. Adding the two translated matrices to the original matrix gives a symmetric rational matrix with the same positive vector at eigenvalue 3ρ. Its rational characteristic polynomial also has the root −3ρ. The two eigenvectors force the ratio of their entries to alternate in sign along every positive edge. Connectivity propagates a nonzero ratio to every vertex. Replacing the last edge of a path to the permuted vertex would produce an odd closed walk if the permutation changed its color.")),
                Paragraph(Text("For Hong, Wu and Xia’s Problem 2, suppose a connected cubic support in Q9 has unsigned weighted adjacency with Perron value equal to the Euclidean weight norm for every positive coordinate weighting. If an affine cube symmetry stabilizing that support has a proper nonempty invariant set I of axes, use weight 2 on I and 1 elsewhere. The squared norm is 9 + 3|I|, which lies strictly between 9 and 36 and is divisible by 3, hence is not a square. If the axis action is a single 9-cycle, a parity-changing stabilizer has a parity-changing ninth power with trivial axis action. This translation falls under the first case with a singleton I. These cases exclude parity-changing stabilizers under the stated weighted saturation assumption. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            Graph + "MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Irreducible"))]));
}
