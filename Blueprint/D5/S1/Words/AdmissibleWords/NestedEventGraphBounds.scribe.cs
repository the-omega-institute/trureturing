using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class NestedEventGraphBoundsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Words/AdmissibleWords/NestedEventGraphBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least downward variation along graph walks bounds the difference from a fixed source.",
        H("Sharp event differences on a graph"),
        Blocks(
            Describe.Lean(DescribeId.Create("cost"), DeclarationHandle.Create(Owner + "distance"),
                H("Least downward variation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For a directed traversal of a graph edge, the cost is the positive part "
                    + "of the decrease in the prescribed mass. The least variation between "
                    + "reachable vertices is the infimum of the sums along all connecting walks."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sharp-difference"),
                DeclarationHandle.Create(Owner + "sharp_difference"),
                H("Simultaneously sharp bounds from a fixed vertex"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Prescribe a mass between zero and one at each vertex and fix a source "
                    + "that can reach every vertex. Take Lebesgue-measurable events in the "
                    + "half-open unit interval and require the two events on each edge to be "
                    + "comparable by inclusion. The mass "
                    + "of the source event outside a target is bounded by the source mass, "
                    + "the target complement mass and the least downward variation. The "
                    + "successive differences on any walk cover the source-to-target difference. "
                    + "For attainment, prescribe the overlap with the source to be the maximum "
                    + "of zero, the sum of the endpoint masses minus one and the source mass "
                    + "minus the least variation. The shortest-walk inequalities make the masses "
                    + "inside and outside the source monotone along each inclusion. The interval "
                    + "construction then attains all the bounds in one family with inclusions "
                    + "ordered by mass and identical events at tied masses on an edge."))),
                DescribeRole.Theorem))));
}
