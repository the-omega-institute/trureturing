using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Scarf;

internal sealed class ColorfulDoorsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/mathxmum2025brouwer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nearly colorful room has exactly two nearly colorful doors.",
        H("A nearly colorful room has exactly two nearly colorful doors"),
        Blocks(Describe.Lean(
            DescribeId.Create("mathxmum-colorfuldoors"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Scarf/ColorfulDoors.doors_of_NCroom"),
            H("A nearly colorful room has exactly two nearly colorful doors"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For arbitrary coloring c of the finite cell, a room missing exactly one color has a set of nearly colorful incident doors equal to a pair of distinct doors. No global injectivity of the coloring is assumed.")),
                Paragraph(Text("If the color image has full cell cardinality, construct an erased-point door and an inserted-color door using the unique external color. If the image has a one-unit deficit, erase either member of the collision pair and use three-collision exclusion to exhaust the doors.")),
                Paragraph(Text("The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion."))),
            DescribeRole.Theorem))));
}
