using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class BinaryCubeHalfKernelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/BinaryCubeHalfKernel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary adjacency on cube halves",
        H("Binary adjacency on cube halves"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjacency"),
                DeclarationHandle.Create(Module + ".adjacency"),
                H("Binary cube adjacency"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum the translated word over all single-coordinate involutions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("adjacency-square"),
                DeclarationHandle.Create(Module + ".adjacency_square"),
                H("Square of binary cube adjacency"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each diagonal term is an involution and each pair of distinct coordinate flips cancels in characteristic two. Thus the square is multiplication by the dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjacency-involutive"),
                DeclarationHandle.Create(Module + ".adjacency_involutive"),
                H("Odd-dimensional adjacency is an involution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An odd number of diagonal terms remains after the cancellation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjacency-eq-zero-iff-half"),
                DeclarationHandle.Create(Module + ".adjacency_eq_zero_iff_half"),
                H("An even-dimensional kernel word is determined by one half"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two half-cube equations reduce to one because odd-dimensional adjacency is an involution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjacency-add-eq-zero-iff-affine-half"),
                DeclarationHandle.Create(Module + ".adjacency_add_eq_zero_iff_affine_half"),
                H("Reconstructing a kernel completion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The affine formula determines the second half of the unknown word after adding the prescribed word. " +
                    "For Hong–Wu–Xia, arXiv:2610.09483 §7, Problem 2, the prescribed word can be the occupied singleton contacts of an axial fold."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjacency-two-sections-eq"),
                DeclarationHandle.Create(Module + ".adjacency_two_sections_eq"),
                H("The four section equations for two deleted coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coordinate flips along the first two axes move between adjacent sections. " +
                    "The remaining flips act within each section, so each section equation relates these three contributions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjacency-opposite-sections-zero"),
                DeclarationHandle.Create(Module + ".adjacency_opposite_sections_zero"),
                H("Opposite sections give a lower-dimensional kernel word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two section equations have the same adjacent sections. Adding them in characteristic two cancels those terms. " +
                    "When the sum is nonzero, its support is bounded below by the minimum kernel weight in the smaller cube."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum"))]));
}
