using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;
internal sealed class MiuraEqualityNeutralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual-array geometric equality for the original Miura residual class.", H("MiuraEqualityNeutral"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraequalityneutral-1"),
                DeclarationHandle.Create(Prefix + "equality_neutral_extremum_interior"), H("equality neutral extremum interior"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. Every individual extremum belonging to the actual neutral-row support is strictly internal on both physical axes: its row index is positive and its successor is less than m, and its column index is positive and its successor is less than n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalityneutral-2"),
                DeclarationHandle.Create(Prefix + "equality_first_minimum_in_minimum_slab"), H("equality first minimum in minimum slab"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If the physical top-row profile has exactly one one-dimensional local maximum, including endpoints, then any specified ambient minimum whose row precedes no other ambient minimum belongs to a minimum-type row slab. A minimum-free prefix is a descending extrusion of the same top profile; the profile minimum is therefore at a physical column endpoint, where equality forbids neutral incidence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalityneutral-3"),
                DeclarationHandle.Create(Prefix + "equality_no_neutral_of_boundary_peaks"), H("equality no neutral of boundary peaks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one minimum row slab and the actual physical top and bottom profiles each have exactly one one-dimensional local maximum, then both the neutral row-slab family and the neutral column-slab family are empty. The earliest and latest ambient minima belong to the same minimum slab and bound all actual minima. Every hypothetical neutral slab supplies an actual minimum, contradicting disjointness of the canonical slabs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalityneutral-4"),
                DeclarationHandle.Create(Prefix + "equality_boundary_maximum_profiles"), H("equality boundary maximum profiles"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one maximum column slab and specified maximum row slabs contain the physical first and last rows, respectively, then the physical top and bottom profiles each have exactly one local maximum including endpoints. Saturation supplies unique actual maxima; boundary strip rigidity lifts every profile maximum to an ambient maximum in its specified slab."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalityneutral-5"),
                DeclarationHandle.Create(Prefix + "equality_crossed_no_neutral"), H("equality crossed no neutral"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If there is exactly one minimum row slab and exactly one maximum column slab, and specified maximum row slabs contain the physical first and last rows, respectively, then both actual neutral slab families are empty. The required profile uniqueness is derived from these actual boundary slabs."))), DescribeRole.Theorem))));
}
