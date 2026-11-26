using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.FiniteGeometry;

internal sealed class DoubledTriangleFoldsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum-fold colorings of doubled triangles",
        H("Minimum-fold colorings of doubled triangles"),
        Blocks(Describe.Lean(
            DescribeId.Create("doubled-triangle-minimum-fold-uniqueness"),
            DeclarationHandle.Create(
                "D5/S0/FiniteGeometry/DoubledTriangleFolds.minimum_fold_uniqueness"),
            H("Equality forces the two-sided coloring"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/FiniteGeometry/fernando2026goodcolorings")),
            Blocks(
                Paragraph(Text(
                    "For every positive side length n, a coloring is good and has exactly 3n folds " +
                    "if and only if its front faces all have one color and its back faces all have " +
                    "the opposite color. Goodness requires the signed difference in incident " +
                    "black and white face corners to be divisible by three at every glued vertex. " +
                    "The identity symmetry suffices, with a global swap when the front is white.")),
                Paragraph(Text(
                    "Up and down cells are indexed by barycentric triples of sum n minus one " +
                    "and n minus two, respectively. Each up cell and omitted corner specifies an " +
                    "edge on each sheet when the corresponding coordinate is positive. At zero " +
                    "there is one seam edge and the two incident up cells lie on opposite sheets. " +
                    "In particular, side length one has two faces and three distinct seam edges.")),
                Paragraph(Text(
                    "A monochromatic ring would force every successive ring toward the corner to " +
                    "have that color. The vertex congruence first fixes both faces at the seam, " +
                    "then propagates across each sheet through triples of consecutive faces. The " +
                    "two corner faces have different colors. In a closed traversal of a " +
                    "nonmonochromatic ring, a rise and a fall in color occur at different edges. " +
                    "Every fold crosses two coordinate cuts, so there are at least 3n folds. " +
                    "At equality each cut has exactly two.")),
                Paragraph(Text(
                    "At each side, the two corner folds leaving the side exhaust the nearest " +
                    "parallel cut. The up, down, up fans joining consecutive side faces on " +
                    "each sheet therefore use unfolded edges. Both sheets retain their first " +
                    "corner colors along the side, so every seam edge folds. The seam count " +
                    "exhausts the total of 3n and the remaining edges are unfolded. Moving one " +
                    "unit of barycentric mass toward a fixed corner connects all up cells " +
                    "through down cells within each sheet, and every down cell joins an up cell.")),
                Paragraph(Text(
                    "Conversely, the opposite uniform sheets balance their incident corners at " +
                    "boundary vertices. Each interior vertex has six corners of one color. " +
                    "Exactly the seam edges fold, giving 3n folds."))),
            DescribeRole.Theorem))));
}
