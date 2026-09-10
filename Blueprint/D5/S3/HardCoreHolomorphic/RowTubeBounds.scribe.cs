using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HardCoreHolomorphic;

internal sealed class RowTubeBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit holomorphic hard-core coordinates and uniform complex neighborhoods.",
        H("RowTubeBounds"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-holo-rowtubebounds-coeff-bound"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/RowTubeBounds.CoeffBound"),
                H("CoeffBound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixed numerical coefficient range, satisfied by the actual 881 types."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-holo-rowtubebounds-row-tube-bounds"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/RowTubeBounds.row_tube_bounds"),
                H("row tube bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bounds are uniform in every child subset of cardinality at most four. Real-row contraction is consumed later; these estimates use only coefficient ranges."))), DescribeRole.Theorem))));
}
