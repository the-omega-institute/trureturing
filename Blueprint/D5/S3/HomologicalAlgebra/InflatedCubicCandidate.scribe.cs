using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class BarnesWallInflatedCubicCandidateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Involution restrictions and the Barnes–Wall anomaly candidates",
        H("Two candidates after inflation to the sign extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("barnes-wall-inflated-cubic-candidate"),
            DeclarationHandle.Create(
                "D5/S3/HomologicalAlgebra/InflatedCubicCandidate.circle_inflation_has_two_candidates"),
            H("Cocycles trivial on involution subgroups reduce to a single bit"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/keller2026barneswall")),
            Blocks(Paragraph(Text(
                "The cyclic diagonal is a cubic polynomial. The involution restrictions force it " +
                "to vanish on the split quadratic zero cone, so it is the quadratic form times " +
                "an affine linear function. The sign coordinate gives a primitive for the " +
                "linear part after inflation."))),
            DescribeRole.Theorem))));
}
