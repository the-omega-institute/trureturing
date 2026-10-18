using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class UnitarilyInvariantNormDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/UnitarilyInvariantNorm";
    private static LibraryNoteRef Background => LibraryNoteRef.Create("D5/L/Eigenstructure/bhatia1997matrixanalysis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitarily invariant norms and symmetric diagonal gauges.",
        H("Unitarily invariant norms and symmetric diagonal gauges"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zhangli-unitarilyinvariantnorm-uinorm"),
                DeclarationHandle.Create(Module + ".UINorm"),
                H("Unitarily invariant complex matrix norms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For each natural n, UINorm consists of a real-valued function N on complex n by n matrices that is nonnegative, vanishes exactly at zero, is subadditive, satisfies N(cX)=|c|N(X) for every complex scalar c, and satisfies N(UXV)=N(X) for unitary U and V."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zhangli-unitarilyinvariantnorm-n-eq-singularvalues"),
                DeclarationHandle.Create(Module + ".N_eq_singularValues"),
                H("Symmetric gauge representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every complex square matrix X, N(X)=N(diag(s(X))), where s(X) is its nonnegative singular-value vector. Thus the real diagonal gauge γ(x)=N(diag(x)) represents N as γ(s(X)); no ordering of the singular values is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-unitarilyinvariantnorm-n-conjtranspose"),
                DeclarationHandle.Create(Module + ".N_conjTranspose"),
                H("Adjoint invariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every complex square matrix X, N(X*)=N(X). Singular-value decomposition exchanges the two unitary factors and preserves the nonnegative diagonal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-unitarilyinvariantnorm-n-transpose"),
                DeclarationHandle.Create(Module + ".N_transpose"),
                H("Transpose invariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every complex square matrix X, N(Xᵀ)=N(X), including matrices with nonreal entries. Transposing a singular-value decomposition preserves its diagonal and gives unitary factors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-unitarilyinvariantnorm-n-diagonal-contract"),
                DeclarationHandle.Create(Module + ".N_diagonal_contract"),
                H("Coordinate contractions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For real vectors x and c with |cᵢ|≤1 at every coordinate, N(diag(cᵢxᵢ))≤N(diag(x)). A convex combination with a diagonal sign reflection contracts one coordinate, and iteration contracts them all."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-unitarilyinvariantnorm-n-diagonal-mono"),
                DeclarationHandle.Create(Module + ".N_diagonal_mono"),
                H("Absolute coordinate domination"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For real vectors x and y satisfying |xᵢ|≤|yᵢ| at every coordinate, N(diag(x))≤N(diag(y)). Zero coordinates are permitted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-unitarilyinvariantnorm-n-diagonal-perm"),
                DeclarationHandle.Create(Module + ".N_diagonal_perm"),
                H("Permutation invariance of the gauge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For every real vector x and every permutation σ, N(diag(x∘σ))=N(diag(x)). Permutation conjugation preserves the norm."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-unitarilyinvariantnorm-n-diagonal-permmatrix"),
                DeclarationHandle.Create(Module + ".N_diagonal_permMatrix"),
                H("The gauge of a permutation matching"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For real diagonal weights a and b and a permutation matrix Pσ whose row i has its nonzero entry at column σ(i), N(diag(a)Pσdiag(b))=N(diag(aᵢbσ(i))). No sign assumption on the weights is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-unitarilyinvariantnorm-n-diagonal-weakmajorization"),
                DeclarationHandle.Create(Module + ".N_diagonal_weakMajorization"),
                H("Fan dominance for diagonal gauges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("Let z and q be nonnegative real vectors, with z decreasing. If every initial sum of z is at most the corresponding initial sum of q, then N(diag(z))≤N(diag(q)). In particular, weak majorization of decreasing nonnegative vectors implies the norm inequality; the stated hypothesis does not require q to be decreasing."))),
                DescribeRole.Theorem))));
}
