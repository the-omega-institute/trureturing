using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraSlabSignsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraSlabSigns.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frozen cuts force both nonneutral signs among actual occupied slabs.", H("Existence of minimum and maximum slab types"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraslabsigns-minimum"),
                DeclarationHandle.Create(Prefix + "minimum_row_slab_exists"), H("A minimum-type slab exists"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual unit-edge array with at least two rows, at least one column and an unoccupied row, its canonical minimum-type row slab family is nonempty. If the earliest positive frozen slope has no earlier frozen row, the top occupied slab is minimum type. Otherwise the last preceding negative frozen row and the earliest positive frozen row enclose a minimum-type occupied slab. If there is no positive frozen slope, the last frozen row has negative slope and the bottom slab is minimum type."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabsigns-maximum"),
                DeclarationHandle.Create(Prefix + "maximum_row_slab_exists"), H("A maximum-type slab exists"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same actual-array assumptions, the canonical maximum-type row slab family is nonempty. Negation preserves the occupied interval family and exchanges the minimum and maximum outward cut signs."))), DescribeRole.Theorem))));
}
