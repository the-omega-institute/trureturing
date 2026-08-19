using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicNine;

internal sealed class EnumerationNineAggregateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Call("IsGreatest",
            Id("tribonacciPeriodicOrbitMinimaNine"),
            Call("championValue", Id("t")));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineAggregate.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The period-at-most-nine enumeration has maximin exactly the champion value.",
            H("Period Nine Aggregate"),
            Blocks(
                Paragraph(Text(
                    "The period-nine level already carried validity, twenty-six per-orbit low-arm "
                        + "bounds, and pairwise distinctness. What it did not carry was the shape "
                        + "the optimality statement consumes: a cumulative representative list "
                        + "through period nine, and the membership of each recorded low state in "
                        + "its own orbit. Both are supplied here, and the aggregate follows by "
                        + "the same argument the period-eight level uses.")),
                Paragraph(Text(
                    "The consequence of the omission was that the source sentence's claim, that "
                        + "the enumeration up to period eleven exhibits the optimal cycle, had a "
                        + "formal counterpart only up to period eight. The parts existed at nine, "
                        + "ten and eleven; the conjunction over the cumulative list did not.")),
                Describe.Lean(
                    DescribeId.Create("period-nine-maximin-is-the-champion-value"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_periodic_orbit_maximin_nine"),
                    H("Period nine maximin is the champion value"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The greatest element is attained by the period-two repeating orbit, "
                            + "which is inherited from the shorter levels rather than new at "
                            + "nine. What nine contributes is that none of its twenty-six new "
                            + "classes beats it."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight")),
            ]));
    }
}
