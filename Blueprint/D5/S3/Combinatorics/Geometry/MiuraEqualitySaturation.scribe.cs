using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;
internal sealed class MiuraEqualitySaturationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual-array geometric equality for the original Miura residual class.", H("MiuraEqualitySaturation"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraequalitysaturation-1"),
                DeclarationHandle.Create(Prefix + "equality_nonneutral_extremum"), H("equality nonneutral extremum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid, with m at least two and n positive, assume that the individual-extremum count equals the neutral row-slab count plus the neutral column-slab count plus the product of the minimum row and column slab counts plus the product of the maximum row and column slab counts. Every individual extremum outside the union of the neutral row and column support sets lies either in a minimum row slab and a minimum column slab and is an ambient strict minimum, or in a maximum row slab and a maximum column slab and is an ambient strict maximum. Equality turns the existing matching-cell injection into a bijection, retaining each actual cell."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalitysaturation-2"),
                DeclarationHandle.Create(Prefix + "equality_slab_extrema_sign"), H("equality slab extrema sign"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid, with m at least two and n positive, assume that the individual-extremum count equals the neutral row-slab count plus the neutral column-slab count plus the product of the minimum row and column slab counts plus the product of the maximum row and column slab counts. Every actual minimum-type row slab contains no ambient strict maximum, and every actual maximum-type row slab contains no ambient strict minimum. The two assertions quantify over every cell whose row lies in the specified slab."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraequalitysaturation-3"),
                DeclarationHandle.Create(Prefix + "equality_maximum_slab_unique"), H("equality maximum slab unique"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer unit-edge height array on an m by n grid, with m at least two and n positive, assume that the individual-extremum count equals the neutral row-slab count plus the neutral column-slab count plus the product of the minimum row and column slab counts plus the product of the maximum row and column slab counts. If there is exactly one maximum column slab, each specified maximum row slab contains exactly one actual cell that is an ambient strict maximum."))), DescribeRole.Theorem))));
}
