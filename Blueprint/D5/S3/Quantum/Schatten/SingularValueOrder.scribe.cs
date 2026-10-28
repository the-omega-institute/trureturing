using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class SingularValueOrderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/SingularValueOrder";
    private static LibraryNoteRef Background => LibraryNoteRef.Create("D5/L/Eigenstructure/bhatia1997matrixanalysis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gram order and decreasing singular values.",
        H("Gram order and decreasing singular values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eigenvalues-zero-mono"),
                DeclarationHandle.Create(Module + ".eigenvalues_zero_mono"),
                H("Hermitian eigenvalue order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every dimension, Hermitian complex matrices H,K with K−H positive semidefinite satisfy λᵢ(H)≤λᵢ(K) at every decreasing eigenvalue index. The spectral subspace comparison includes repeated eigenvalues."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eigenvalues-zero-smul"),
                DeclarationHandle.Create(Module + ".eigenvalues_zero_smul"),
                H("Nonnegative eigenvalue scaling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every dimension, Hermitian complex matrix H and nonnegative real q, the decreasing eigenvalues satisfy λᵢ(qH)=qλᵢ(H) at every index. The formula includes q=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-singularvalueorder-singularvaluessorted-eq-sqrt-eigenvalues-zero"),
                DeclarationHandle.Create(Module + ".singularValuesSorted_eq_sqrt_eigenvalues_zero"),
                H("Singular values from Gram eigenvalues"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For each index i, the ith decreasing singular value of a complex square matrix A is the nonnegative square root of the ith decreasing eigenvalue of A*A. Eigenvalues are counted with multiplicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-singularvalueorder-gram-singularvaluessorted-mono"),
                DeclarationHandle.Create(Module + ".gram_singularValuesSorted_mono"),
                H("Courant–Fischer monotonicity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("If B*B−A*A is positive semidefinite, then sᵢ(A)≤sᵢ(B) for every decreasing singular-value index i. Courant–Fischer comparison of the two Hermitian Gram matrices gives the eigenvalue inequality before taking square roots."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-singularvalueorder-singularvaluessorted-unitary-mul"),
                DeclarationHandle.Create(Module + ".singularValuesSorted_unitary_mul"),
                H("Unitary left multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every unitary U and every complex square A, sᵢ(UA)=sᵢ(A) at every decreasing singular-value index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-singularvalueorder-singularvaluessorted-conjtranspose"),
                DeclarationHandle.Create(Module + ".singularValuesSorted_conjTranspose"),
                H("Adjoint singular values"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every complex square A, sᵢ(A*)=sᵢ(A) at every decreasing singular-value index, including zero singular values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-singularvalueorder-singularvaluessorted-smul-nonneg"),
                DeclarationHandle.Create(Module + ".singularValuesSorted_smul_nonneg"),
                H("Nonnegative scalar homogeneity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every nonnegative real r and complex square A, sᵢ(rA)=r sᵢ(A) at every decreasing singular-value index. The formula includes r=0."))),
                DescribeRole.Theorem))));
}
