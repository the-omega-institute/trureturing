using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;
internal sealed class MiuraEqualitySidesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraEqualitySides.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual-array geometric equality for the original Miura residual class.", H("MiuraEqualitySides"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraequalitysides-1"),
                DeclarationHandle.Create(Prefix + "equality_no_neutral_top_minimum"), H("equality no neutral top minimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one maximum row slab, a specified minimum row slab contains the physical first row, and a specified maximum row slab contains the physical last row, then both actual neutral slab families are empty. An extremum of the top profile in a neutral column interval would force a profile minimum there, hence an impermissible ambient minimum on a neutral support at the physical top. The first ambient maximum therefore lies in the bottom maximum slab and excludes every neutral row slab."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalitysides-2"),
                DeclarationHandle.Create(Prefix + "equality_two_row_types_no_neutral"), H("equality two row types no neutral"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one minimum row slab and exactly one maximum row slab, both actual neutral slab families are empty. The physical boundary slabs have opposite types; height negation handles the other top-boundary sign while preserving the same actual neutral intervals."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalitysides-3"),
                DeclarationHandle.Create(Prefix + "equality_two_row_types_minima_boundary"), H("equality two row types minima boundary"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one minimum row slab and exactly one maximum row slab, then all ambient strict minima lie on the physical first row, or all lie on the physical last row. This is one common physical side for the whole minimum set. Saturation and the proved absence of neutral slabs place all minima in the single minimum slab, and the finite one-exit extrusion pushes them to that slab's physical boundary."))), DescribeRole.Theorem))));
}
