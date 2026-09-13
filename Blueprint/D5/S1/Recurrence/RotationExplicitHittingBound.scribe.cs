using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class RotationExplicitHittingBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit rotation mesh bound.",
        H("Explicit rotation mesh bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rotationexplicithittingbound-floor-mesh-seam-gap-bounds"),
                DeclarationHandle.Create("D5/S1/Recurrence/RotationExplicitHittingBound.floor_mesh_seam_gap_bounds"),
                H("The floor mesh seam gap is bounded by one mesh step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive real mesh size h, the gap from the last point of the floor mesh "
                    + "to the unit-circle seam is nonnegative and no larger than h."))),
                DescribeRole.Theorem))));
}
