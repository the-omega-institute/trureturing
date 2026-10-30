using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class LiteralSecondStarCoordinateBoundSharpnessDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Geometry/Gluing/LiteralSecondStarCoordinateBoundSharpness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharpness of the literal second-star coordinate bound",
        H("The literal standard second closed star attains 25/48"),
        Blocks(
            Paragraph(Text(
                "For each original vertex, the equal-weight barycenter of the four "
                    + "parent-flag vertices lies in the corresponding literal closed star "
                    + "and has coordinate exactly 25/48.")),
            Describe.Lean(
                DescribeId.Create("literal-second-star-coordinate-bound-sharp"),
                DeclarationHandle.Create(Root + "literal_standard_closed_star_coordinate_bound_sharp"),
                H("The 25/48 lower bound is attained"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equal-weight barycenter of the four parent-flag vertices is a "
                        + "closed-star point, and its distinguished coordinate is exactly "
                        + "the average 1, 1/2, 1/3, 1/4."))),
                DescribeRole.Theorem)),
        []));
}
