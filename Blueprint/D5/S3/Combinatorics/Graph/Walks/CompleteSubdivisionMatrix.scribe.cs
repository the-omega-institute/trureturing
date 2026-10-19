using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CompleteSubdivisionMatrixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMatrix.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/farhan2026multiset");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric binary matrices with distinct row sums",
        H("Symmetric binary matrices with distinct row sums"),
        Blocks(
            Paragraph(Text("The diagonal is unrestricted. Distinct row sums force a zero row or a full row; symmetry prevents both. With a zero row, ranking the row sums gives a permutation of all indices. The ranked matrix has entry one exactly when the two ranks sum to at least n. The proof deletes the forced zero and last rows and columns and inducts by two, including both initial sizes.")),
            Describe.Lean(DescribeId.Create("complete-subdivision-matrix-ranked-staircase"),
                DeclarationHandle.Create(Prefix + "ranked_staircase"),
                H("ranked staircase"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A symmetric binary matrix whose row i sums to i has entry one exactly at positions whose indices sum to at least n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-matrix-row-sum-le"),
                DeclarationHandle.Create(Prefix + "row_sum_le"),
                H("row sum le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every binary row of length n has sum at most n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-matrix-zero-full-incompatible"),
                DeclarationHandle.Create(Prefix + "zero_full_incompatible"),
                H("zero full incompatible"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A symmetric binary matrix cannot have both a zero row and a full row."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-matrix-distinct-rows-extreme"),
                DeclarationHandle.Create(Prefix + "distinct_rows_extreme"),
                H("distinct rows extreme"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Injective row sums in a positive-size binary matrix contain either zero or n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-matrix-zero-row-normal-form"),
                DeclarationHandle.Create(Prefix + "zero_row_normal_form"),
                H("zero row normal form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A symmetric binary matrix with distinct row sums and a zero row admits an actual rank permutation giving the staircase and exact row ranks."))), DescribeRole.Theorem))));
}
