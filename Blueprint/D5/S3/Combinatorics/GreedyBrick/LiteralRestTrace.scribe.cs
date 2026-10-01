using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GreedyBrick;

internal sealed class LiteralRestTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal capacity trajectory supplies an initialized unbounded rest trace.",
        H("Literal Placements and the Rest Clock"),
        Blocks(
            Paragraph(Text("Capacities in the literal trajectory are ordered from top to bottom; "
                + "rest-state capacities are ordered from bottom to top. The initial rest state "
                + "is endpoint one, capacity list [1], and bin one. This trace theorem relates "
                + "capacity states and brick indices; it does not assert the original OEIS "
                + "self-composition identity.")),
            Describe.Lean(
                DescribeId.Create("greedy-brick-literal-rest-trace"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/GreedyBrick/LiteralRestTrace.literal_trace_realization"),
                H("An Actual Initialized Unbounded Trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists a RestTrace whose next bin is the first zero "
                    + "of its current capacity list, or the new bin when all current capacities "
                    + "are positive. Its reversed capacity list equals the literal trajectory "
                    + "at every endpoint. The endpoints are strictly increasing and cofinal in "
                    + "the natural brick indices. Every intermediate literal placement agrees "
                    + "with that same trajectory, and every positive brick belongs to an event "
                    + "interval. A recursive block coupling supplies the clock, and literal "
                    + "height totality transfers along its cofinal samples to give unbounded "
                    + "rest height. No RestTrace or unbounded-rest-height premise is assumed."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/GreedyBrick/RestBlock")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/GreedyBrick/EventRealization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ArithSums/GreedyBrickCapacityTotality"))
        ]));
}
