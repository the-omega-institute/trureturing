using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraSlabClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraSlabClassification.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual maximal occupied intervals have minimum, maximum or neutral type.", H("Classification by actual boundary cuts"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraslabclassification-partition"),
                DeclarationHandle.Create(Prefix + "row_slab_card_partition"), H("The three actual types partition the slabs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same actual unit-edge, dimension and frozen-row assumptions, the total row slab cardinality equals the sum of the minimum, maximum and neutral row slab cardinalities. A proper interval cannot have both unit outward signs, and an equal-cut internal interval cannot also have a common nonzero outward sign."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabclassification-type"),
                DeclarationHandle.Create(Prefix + "row_slab_classification"), H("Exhaustive slab types"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every unit-edge integer height array with at least two rows, at least one column and at least one unoccupied row, each maximal occupied row interval is a minimum, maximum or neutral row slab as defined by its actual boundary edges. The frozen row assumption excludes a whole-axis occupied interval. The immediately adjacent outside rows are unoccupied by maximality; physical boundary occupancy makes these rows internal, and the frozen-cut theorem supplies their uniform unit signs. Opposite cut signs give a minimum or maximum type, equal signs give neutral type, and a physical end omits its absent cut."))), DescribeRole.Theorem))));
}
