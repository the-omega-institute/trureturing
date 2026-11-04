using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class LocalOutputGluingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Schatten compression budgets glue over complete orthogonal local output resolutions.",
        H("Local output compression budgets"), Blocks(
            Describe.Lean(
                DescribeId.Create("row-piece-schatten-power-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/LocalOutputGluing.row_piece_schattenPow_sum_le"),
                H("Pinching the actual row maps"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite family of isometric output embeddings whose range projections sum to the identity, and every real 1 <= q <= 2, the sum of the 2q-th Schatten powers of the projected row pieces is bounded by the 2q-th Schatten power of the original arbitrary rectangular complex matrix. The proof applies the existing full PSD positive unital Jensen theorem to each actual Gram matrix, then sums the trace bounds using the complete output resolution. Empty input, output and component dimensions are included."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("column-power-table"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/LocalOutputGluing.columnPowerTable"),
                H("Actual column power table"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two row entries are the actual 2q-th Schatten powers of the two corresponding rectangular complex block maps. Applying Aq to this table recovers the repository norm compression matrix exactly."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-output-compression-budget"),
                DeclarationHandle.Create("D5/S3/Quantum/NormCompression/LocalOutputGluing.local_output_compression_budget"),
                H("Gluing the actual compression budget"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real 1 < q < 2, every finite column family of arbitrary rectangular complex maps, and complete finite isometric resolutions of both local outputs, the sum of the 2q-th Schatten powers of the component compression matrices is bounded by the 2q-th Schatten power of the global compression matrix. The proof uses the proved finite power cone concavity on the actual column power tables and their entrywise domination from row pinching. Local output dimensions and original column dimensions may vary and may be empty. This is the compression budget step of local orthogonal output gluing. It does not assert the remaining unrestricted common majorant optimization or the original Audenaert inequality."))), DescribeRole.Theorem))));
}
