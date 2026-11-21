using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVExtremeAnalyticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV (5,3) lower bound in every finite dimension",
        H("The refined BMV (5,3) lower bound in every finite dimension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-extreme-product-five"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_five"),
                H("The spectral-power trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any pair of positive semidefinite complex matrices A and B in any finite dimension, " +
                    "the mean trace of the 56 words with five copies of A and three copies of B is at least " +
                    "the trace of the cube of A^(5/3) B, where the power of A is defined by spectral calculus. " +
                    "The repository proof uses the eigenvalues of the positive semidefinite cube root of A " +
                    "and splits the cubic trace defect into a cyclic sum of centered kernels. " +
                    "Exact polynomial certificates supply the mixed derivative and boundary signs that make the rectangle differences " +
                    "of the normalized upper kernel nonnegative on each sorted finite sample. The differences telescope, " +
                    "giving a sum of weighted outer products of interval indicators. Diagonal rescaling and a rank-one block below the center " +
                    "give positive semidefinite centered matrices. The Schur product theorem makes each centered walk contribution nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-extreme-exponential-five"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_five"),
                H("The exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any finite-dimensional complex Hermitian pair H and K, the mean trace of the 56 words " +
                    "with five copies of the exponential of H and three copies of the exponential of K is at least " +
                    "the trace of the matrix exponential of 5H + 3K. Hägele raises the lower-bound question in Section 7. " +
                    "The product bound for the two exponentials and the dyadic Lie–Trotter trace comparison from Hägele's Lemma 2 give the result."))),
                DescribeRole.Theorem))));
}
