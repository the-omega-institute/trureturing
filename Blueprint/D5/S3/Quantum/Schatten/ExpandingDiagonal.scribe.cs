using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ExpandingDiagonalDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/ExpandingDiagonal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite matching minimizes expanding diagonal products.",
        H("Opposite matching minimizes expanding diagonal products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zhangli-expandingdiagonal-uinorm-n-diagonal-subsetproducts-le"),
                DeclarationHandle.Create(Module + ".N_diagonal_subsetProducts_le"),
                H("Subset products control a diagonal gauge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let x and y be nonnegative real vectors with y decreasing. Suppose that for every coordinate subset I, the product of x over I is at most the product of the |I| first coordinates of y. Then N(diag(x))≤N(diag(y)) for every unitarily invariant norm N. Sorting x converts the subset bounds to weak log-majorization; power-sum comparison gives weak majorization and hence the gauge inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-expandingdiagonal-uinorm-exists-permutation-expanding-lower-bound"),
                DeclarationHandle.Create(Module + ".exists_permutation_expanding_lower_bound"),
                H("A single minimizing permutation for all expanding factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative real vectors a and b and a unitarily invariant norm N, there exists a permutation σ such that N(diag(a)Pσdiag(b))≤N(diag(a)Tdiag(b)) for every complex square T satisfying T*T−I positive semidefinite. For positive weights, the lower Gelfand–Naimark inequality on arbitrary index subsets compares the opposite matching a↓ᵢb↑ᵢ with the singular values of diag(a)Tdiag(b). Replacing both weights by their sums with a positive ε and taking ε to zero extends the same permutation to zero weights."))),
                DescribeRole.Theorem))));
}
