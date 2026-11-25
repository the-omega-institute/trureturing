using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Latin;

internal sealed class NonnegativePermutationFactorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Latin/NonnegativePermutationFactors.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/mazhang2026factorperfection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "If a product of square nonnegative integer matrices is a permutation matrix, every factor is one.",
        H("Nonnegative integer factors of a permutation matrix"),
        Blocks(
            Describe.Lean(DescribeId.Create("nonnegative-permutation-factors"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every factor of a permutation-matrix product is a permutation matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every size n, including n = 0, and every finite list of n×n matrices "
                    + "with entries in ℕ, if the product of the list is a permutation matrix, "
                    + "then every matrix in the list is a permutation matrix; the empty list "
                    + "satisfies the statement vacuously. The key step: if A·C = 1 for "
                    + "nonnegative integer matrices A and C, then also C·A = 1 since square "
                    + "matrices are Dedekind-finite. For each column k, the diagonal entry "
                    + "(C·A)(k,k) = 1 gives a row g(k) with C(k,g(k))·A(g(k),k) > 0. If "
                    + "A(i,k) > 0 with i ≠ g(k), the off-diagonal entry (A·C)(i,g(k)) = 0 would "
                    + "contain the positive term A(i,k)·C(k,g(k)); so column k of A is supported "
                    + "at g(k) only, and (C·A)(k,k) = 1 then forces A(g(k),k) = 1. The "
                    + "diagonal of A·C shows every row of A is nonzero, so g is surjective and "
                    + "hence a bijection, and A is the permutation matrix of g⁻¹. For a "
                    + "product A·B equal to a permutation matrix P, the identities "
                    + "A·(B·P⁻¹) = 1 and B·(P⁻¹·A) = 1 make both factors permutation matrices, "
                    + "and induction on the list finishes the proof."))),
                DescribeRole.Theorem))));
}
