using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;
internal sealed class MiuraEqualitySaturationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality realizes the actual matching rectangles.", H("Saturated geometric slab charge"),
        Blocks(Describe.Lean(DescribeId.Create("miuraequalitysaturation-classify"),
            DeclarationHandle.Create(Prefix + "equality_nonneutral_extremum"), H("Actual nonneutral extrema match their slab types"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid with m at least two and n positive, suppose its number of individual extrema equals the neutral row-slab count plus the neutral column-slab count plus the product of minimum row and column slab counts plus the product of maximum row and column slab counts. Every actual extremum outside the union of the two neutral support sets then lies either in a minimum row slab and a minimum column slab and is an ambient strict minimum, or in a maximum row slab and a maximum column slab and is an ambient strict maximum. The matching-cell injection becomes a bijection by equality of finite cardinalities; parallel extrema retain their distinct actual cells. This is an internal ingredient of the geometric equality classification, whose full endpoint remains open."))), DescribeRole.Theorem))));
}
