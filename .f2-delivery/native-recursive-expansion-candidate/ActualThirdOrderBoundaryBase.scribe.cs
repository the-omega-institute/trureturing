using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualThirdOrderBoundaryBaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualThirdOrderBoundaryBase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eight literal third-order joint paths construct both four-path boundaries of the same actual cycle.",
        H("Initializing the Third Actual Boundary Order"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-third-order-boundary-base"),
                DeclarationHandle.Create(Prefix + "actual_third_order_boundary_base"),
                H("Initialize Both Actual Third-Order Boundaries"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sixteen distinct labelled ports specify the two groups of four real cuts. The supplied current Hamilton cycle is partitioned by its eight actual joint paths. Restore each opposite group with explicit walk append, reversal and seam cons operations. The resulting primary and opposite four-path families exhaust that same cycle and delete precisely their own cut groups. The output also exposes the literal crossing and distinguished prefix of the first opposite boundary, for the subsequent simultaneous update."))), DescribeRole.Theorem))));
}
