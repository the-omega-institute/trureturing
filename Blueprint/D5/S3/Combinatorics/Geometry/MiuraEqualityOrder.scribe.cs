using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;
internal sealed class MiuraEqualityOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual-array geometric equality for the original Miura residual class.", H("MiuraEqualityOrder"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraequalityorder-1"),
                DeclarationHandle.Create(Prefix + "minimum_slab_between_maximum_slabs"), H("minimum slab between maximum slabs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array with at least two rows and at least one column, any specified maximum row slabs A and B with the last row of A strictly before the first row of B have a minimum row slab I strictly between them: the first row of I is after the last row of A and the last row of I is before the first row of B. Its signed transition is selected from genuinely unoccupied rows, using the existing frozen-cut suppliers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalityorder-2"),
                DeclarationHandle.Create(Prefix + "boundary_maximum_slabs"), H("boundary maximum slabs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array with at least two rows, at least one column and a genuinely unoccupied row, if there is exactly one minimum row slab and at least two maximum row slabs, then maximum row slabs contain the physical first and last rows, respectively. The intervening minimum slab between two maxima is internal, so the unique minimum slab cannot be a boundary slab."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalityorder-3"),
                DeclarationHandle.Create(Prefix + "one_minimum_slab_maximum_card_le_two"), H("one minimum slab maximum card le two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array with at least two rows and at least one column, exactly one minimum row slab implies at most two maximum row slabs. Distinct maximum slabs must straddle that unique minimum slab; their position relative to it gives an injection into a two-element type."))), DescribeRole.Theorem))));
}
