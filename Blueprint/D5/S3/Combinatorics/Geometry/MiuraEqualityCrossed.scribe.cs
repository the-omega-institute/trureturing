using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;
internal sealed class MiuraEqualityCrossedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraEqualityCrossed.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual-array geometric equality for the original Miura residual class.", H("MiuraEqualityCrossed"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraequalitycrossed-1"),
                DeclarationHandle.Create(Prefix + "crossed_equality_four"), H("crossed equality four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If the ordered counts of minimum row slabs, maximum row slabs, minimum column slabs and maximum column slabs are either (1,2,2,1) or (2,1,1,2), the actual array has exactly four individual extrema. The first pattern derives its boundary slabs and excludes neutral slabs; height negation proves the other pattern without exchanging physical sides."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalitycrossed-2"),
                DeclarationHandle.Create(Prefix + "equality_two_slabs_or_four"), H("equality two slabs or four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. Either the row axis has exactly one minimum slab and one maximum slab, or the column axis has exactly one minimum slab and one maximum slab, or the individual-extremum count is exactly four. Product saturation, actual slab order and the proved crossed-pattern classification exhaust the alternatives."))), DescribeRole.Theorem))));
}
