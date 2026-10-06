using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Scarf;

internal sealed class IncidenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/mathxmum2025brouwer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An internal door has exactly two incident rooms.",
        H("An internal door has exactly two incident rooms"),
        Blocks(Describe.Lean(
            DescribeId.Create("mathxmum-incidence"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Scarf/Incidence.internal_door_two_rooms"),
            H("An internal door has exactly two incident rooms"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For finite T and indexed linear orders, every internal door admits two distinct incident room pairs; every incident room equals one of them. The incidence relation includes both inserting a point and erasing an index.")),
                Paragraph(Text("The two colliding minimum indices give disjoint M sets. For each nonempty M set insert its actual maximal point; for an empty M set erase the corresponding index. All four branches construct distinct rooms and exclude every other incident room.")),
                Paragraph(Text("The result and proof source are attributed to Math_XMUM's MIT-licensed Brouwer repository at its immutable revision. No mathematical novelty is claimed. The combinatorics and real fixed-point argument establish no tetrahedral geometry, marked gluing, trajectory invariance, uniqueness, geometric Hessian, or convergence conclusion."))),
            DescribeRole.Theorem))));
}
