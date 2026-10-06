using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Scarf;

internal sealed class ColorfulCellDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/mathxmum2025brouwer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scarf colorful dominant-cell existence.",
        H("Scarf colorful dominant-cell existence"),
        Blocks(Describe.Lean(
            DescribeId.Create("mathxmum-colorfulcell"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Scarf/ColorfulCell.Scarf"),
            H("Scarf colorful dominant-cell existence"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For finite inhabited T and I, decidable equalities, any indexed linear orders on T and any coloring c:T->I, the finite set of dominant pairs (sigma,C) satisfying c(sigma)=C is nonempty.")),
                Paragraph(Text("For a fixed color there is one exterior incidence. Every internal-door fiber has cardinality two, and every noncolorful-room fiber has cardinality two. Counting the same incidence set in both directions makes the colorful contribution odd, yielding an actual colorful cell.")),
                Paragraph(Text("The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion."))),
            DescribeRole.Theorem))));
}
