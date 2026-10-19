using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class BasicDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/Basic.";
    private static LibraryNoteRef Original => LibraryNoteRef.Create("D5/L/Entropy/jozsa1994subentropy");
    private static LibraryNoteRef Later => LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subentropy through a determinant integral, with rectangular Gram and isometric invariance.",
        H("Determinant-integral subentropy"),
        Blocks(
            Paragraph(Text("All index types are finite with decidable equality. The ordinary complex matrix underlying a canonical density state is obtained with CStarMatrix.ofMatrix.symm. The integral is a real Lebesgue integral over the open positive half-line. Statements concerning arbitrary matrices assert algebraic invariance; the physical subentropy interpretation is restricted to positive matrices of trace one.")),
            Item("subentropyKernel", "The determinant kernel", "For t>0, K(A,t)=t/(1+t)−1/Re det(I+A/t). On a diagonal matrix with entries p, the reciprocal determinant is the product of t/(t+p_i).", false),
            Item("matrixSubentropy", "The determinant integral", "Q(A) is the integral of K(A,t) over t>0. This determinant representation handles zero eigenvalues and repeated eigenvalues directly.", false),
            Describe.Lean(DescribeId.Create("subentropy"), DeclarationHandle.Create(Owner + "subentropy"),
                H("Subentropy of a density state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Original),
                Blocks(Paragraph(Text("Subentropy is evaluated on the ordinary matrix underlying the canonical DensityState. The determinant-integral representation is a repository derivation of the spectral quantity introduced by Jozsa, Robb and Wootters and studied by Datta and collaborators. The positive simple-spectrum formula is proved in SpectralFormula, and continuity on the full density-matrix domain is proved in DensityKernel."))), DescribeRole.Definition),
            Item("kernel_rectangular_gram", "Rectangular Gram kernels", "For every rectangular complex matrix V and every real t, the kernels of V*V and VV* coincide. The determinant identity det(I+AB)=det(I+BA) proves this without a positivity, invertibility or trace hypothesis."),
            Item("matrixSubentropy_rectangular_gram", "Rectangular Gram invariance", "Integration of the pointwise kernel identity gives Q(V*V)=Q(VV*) in arbitrary finite rectangular dimensions."),
            Item("matrixSubentropy_isometric_embedding", "Isometric embedding invariance", "If J*J=I, then Q(JAJ*)=Q(A). The proof uses the rectangular determinant identity with factors JA and J*, and thus does not require a matrix square root."),
            Item("matrixSubentropy_pure", "Pure states have zero subentropy", "If the squared complex norm of v is one, its rank-one matrix vv* has subentropy zero. Its scalar Gram matrix is the one-dimensional identity, whose determinant kernel vanishes on the positive half-line."),
            Item("kernel_diagonal", "Classical product kernel", "For a real vector p and t nonzero, the kernel of diagonal p is t/(1+t) minus the product of t/(t+p_i). No positivity assumptions enter this algebraic identity."))));

    private static DocumentBlock.Describe Item(string name, string title, string text, bool theorem = true) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Later),
            Blocks(Paragraph(Text(text))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
