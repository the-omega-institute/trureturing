using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class DisjointSpectralSuppliersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flat factors and spectral Jensen bounds",
        H("Flat factors and spectral Jensen bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-flat-rows-of-rank-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers.exists_flat_rows_of_rank_le"),
                H("Flat factors with arbitrary row capacity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/HilbertOperators/lipoon2003principalsubmatrices"),
                    LibraryNoteRef.Create("D5/L/HilbertOperators/massey2010noncommutativeschurhorn")),
                Blocks(
                    Paragraph(Text("A positive semidefinite matrix A with rank at most m has a factor V with m rows, V†V = A and constant diagonal Tr(A)/m in VV†. The positive-capacity construction uses Fourier columns. When m = 0, A is zero and the row type is empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gram-spectral-sum-le-diagonal"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/DisjointSpectralSuppliers.gram_spectral_sum_le_diagonal"),
                H("Concave sums of Gram eigenvalues"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If V†V is a contraction, a concave function on [0,1] vanishing at zero can be summed on the column Gram and bounded by its sum on the row Gram diagonal. The rectangular spectrum comparison establishes the upper spectral endpoint for the row Gram, and diagonal Jensen uses the squared moduli of its diagonalizing unitary."))),
                DescribeRole.Theorem))));
}
