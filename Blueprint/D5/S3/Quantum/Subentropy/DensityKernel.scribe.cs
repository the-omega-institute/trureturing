using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class DensityKernelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/DensityKernel.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integrable common bound and continuity of subentropy on the full density-matrix domain.",
        H("Density-matrix kernels and continuity"),
        Blocks(
            Paragraph(Text("All finite dimensions are allowed. Matrices are positive semidefinite with complex trace one. Their real eigenvalues are nonnegative and sum to one. Unitary diagonalization gives det(I+A/t) as the product of 1+lambda_i/t, so the determinant has positive real part whenever t>0.")),
            Item("spectral_prob", "The spectral probability vector", "A positive semidefinite finite matrix of trace one has nonnegative real eigenvalues summing to one. Positivity supplies the coordinate signs and taking real parts of the spectral trace identity supplies normalization. This interface is used by the Gaussian matrix representation."),
            Item("density_kernel_bounds", "A dimension-independent bound", "The determinant kernel is nonnegative and at most 1/(1+t)^2 for every positive t and every density matrix. The estimate follows from the sharper classical vertex bound after spectral reduction. It includes repeated eigenvalues and zero eigenvalues."),
            Item("integrable_subentropy_kernel", "Absolute integrability", "The continuous kernel on the positive half-line is dominated in absolute value by the common integrable inverse-square function. Hence its defining subentropy integral is absolutely convergent."),
            Item("continuousOn_matrixSubentropy", "Continuity at all density matrices", "The determinant is continuous in the entries, and its real part remains positive on the density domain at each positive t. Dominated convergence with the common function 1/(1+t)^2 gives continuity of Q on the full set of positive trace-one matrices, including its boundary."))));
    private static DocumentBlock.Describe Item(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
