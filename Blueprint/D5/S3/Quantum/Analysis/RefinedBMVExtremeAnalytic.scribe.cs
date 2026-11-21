using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVExtremeAnalyticDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bound at first degrees five through seven",
        H("The refined BMV lower bound at first degrees five through seven in every finite dimension"),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-extreme-product-six"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_six"),
                H("Six copies of the first factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite complex matrices A and B in any finite dimension, " +
                    "the mean trace of the 84 words with six copies of A and three of B is at least " +
                    "the trace of the cube of A^(6/3) B. The first matrix may be singular and may have any number of distinct eigenvalues. " +
                    "The exact coefficient signs at this degree give positive semidefiniteness of the normalized upper kernel " +
                    "by the finite interval Gram argument. The cyclic decomposition and Schur product then give the trace inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-extreme-exponential-six"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_six"),
                H("The exponential comparison at degree six"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For complex Hermitian H and K in any finite dimension, the same word mean on exp H and exp K " +
                    "is bounded below by the trace of exp(6H + 3K). Apply the product comparison to the two exponentials " +
                    "and then use the dyadic trace comparison from Hägele's Lemma 2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-extreme-product-seven"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.product_bound_seven"),
                H("Seven copies of the first factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite complex matrices A and B in any finite dimension, " +
                    "the mean trace of the 120 words with seven copies of A and three of B is at least " +
                    "the trace of the cube of A^(7/3) B. The first matrix may be singular and may have any number of distinct eigenvalues. " +
                    "The exact coefficient signs at this degree give positive semidefiniteness of the normalized upper kernel " +
                    "by the finite interval Gram argument. The cyclic decomposition and Schur product then give the trace inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-extreme-exponential-seven"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVExtremeAnalytic.exponential_bound_seven"),
                H("The exponential comparison at degree seven"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For complex Hermitian H and K in any finite dimension, the same word mean on exp H and exp K " +
                    "is bounded below by the trace of exp(7H + 3K). Apply the product comparison to the two exponentials " +
                    "and then use the dyadic trace comparison from Hägele's Lemma 2."))),
                DescribeRole.Theorem))));
}
