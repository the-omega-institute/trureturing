using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Scarf;

internal sealed class DominanceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/mathxmum2025brouwer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dominance after erasing an index.",
        H("Dominance after erasing an index"),
        Blocks(Describe.Lean(
            DescribeId.Create("mathxmum-dominance"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Scarf/Dominance.isDominant_erase_iff_M_set_empty"),
            H("Dominance after erasing an index"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For finite T with an indexed family of linear orders and a nonempty door (tau,D), each i in D preserves dominance after erasure exactly when it lies in a collision pair of coordinate minima and M_i is empty. Each minimum is taken directly in its corresponding indexed linear order. The quantified pair and the empty-set condition are both required.")),
                Paragraph(Text("Coordinate minima cover every dominant cell. The one-unit deficit supplies a collision pair; an erasure away from that pair leaves a noninjective image with insufficient cardinality. Emptiness of M_i gives the reverse dominance implication.")),
                Paragraph(Text("The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion."))),
            DescribeRole.Theorem))));
}
