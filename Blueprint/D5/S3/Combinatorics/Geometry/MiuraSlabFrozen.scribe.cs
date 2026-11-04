using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraSlabFrozenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraSlabFrozen.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary occupancy and uniform actual cuts around an extrema-free row.", H("Finite frozen-cut suppliers"),
        Blocks(
            Paragraph(Text("The finite walk and frozen-column proofs are adapted from Chakshu Gupta's accompanying CC BY 4.0 Lean source at commit 0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11. They are applied to the transposed original array. Full license terms and attribution accompany the source.")),
            Describe.Lean(DescribeId.Create("miuraslabfrozen-boundary"),
                DeclarationHandle.Create(Prefix + "boundary_rows_occupied"), H("Physical boundary rows contain extrema"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every unit-edge integer height array with at least two rows and one column has an ambient minimum or maximum on each physical boundary row. The finite boundary-walk result is applied to the same transposed array."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraslabfrozen-cuts"),
                DeclarationHandle.Create(Prefix + "inactive_row_uniform_cuts"), H("Uniform cuts at an actual unoccupied row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every unit-edge integer array with at least one column, an internal row containing no ambient extremum has one common downward unit increment on both incident full-width cuts. The increment is either one or minus one. The finite extrema-free walk result first makes the two neighbours symmetric, and the frozen-column slope result makes the sign constant across all columns."))), DescribeRole.Theorem))));
}
