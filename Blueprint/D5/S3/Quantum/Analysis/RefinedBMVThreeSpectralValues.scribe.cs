using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVThreeSpectralValuesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refined BMV lower bounds with three spectral values",
        H("Refined BMV lower bounds with three spectral values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-three-spectral-operator-walk"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.operator_walk_nonneg"),
                H("The three-label inequality for positive matrix factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Cyclicity and conjugate reversal pair the mixed terms. At each of the three labels, Hilbert–Schmidt Cauchy–Schwarz and the arithmetic–geometric mean bound the mixed trace by the two repeated-label traces with their coefficient weights."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-three-spectral-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.product_bound"),
                H("The strong product bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any two finite-dimensional positive semidefinite complex matrices, with at most three distinct eigenvalues of the first matrix, the mean trace of the words with five, six, or seven first factors and three second factors is at least the trace of the cube of the product using spectral power p/3 of the first matrix. The square root of the second matrix compresses each spectral projection into a positive factor. The three-label pairing uses the scalar coefficient certificate for the ordered eigenvalue cube roots."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-three-spectral-exponential"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVThreeSpectralValues.exponential_bound"),
                H("The exponential lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any finite-dimensional Hermitian pair whose first matrix has at most three distinct eigenvalues, the same word counts applied to the matrix exponentials give a lower bound by the trace of the exponential of p times the first matrix plus three times the second matrix. The exact dyadic Lie–Trotter comparison connects the cube estimate to this exponential, as in Hägele's Lemma 2. Section 7 discusses the case with five first factors."))),
                DescribeRole.Theorem))));
}
