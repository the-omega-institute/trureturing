using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEleven;

internal sealed class EnumerationElevenAggregateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var statement = Call("IsGreatest",
            Id("tribonacciPeriodicOrbitMinimaEleven"),
            Call("championValue", Id("t")));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenAggregate.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The period-at-most-eleven enumeration has maximin exactly the champion value.",
            H("Period Eleven Aggregate"),
            Blocks(
                Paragraph(Text(
                    "This level already carried its representative list and its aggregate "
                        + "low-arm bound, under names that do not follow the period-eight "
                        + "convention. Both were found by looking before building, and neither "
                        + "is rebuilt here.")),
                Paragraph(Text(
                    "What was missing is the pair that was missing at every level past eight: "
                        + "each recorded low state's membership in its own orbit, and the "
                        + "cumulative list with its optimality statement. "
                        + "The seventy-four new classes "
                        + "are joined to the period-at-most-ten list, and the argument is the "
                        + "one the period-eight level already uses.")),
                Describe.Lean(
                    DescribeId.Create("period-eleven-maximin-is-the-champion-value"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_periodic_orbit_maximin_eleven"),
                    H("Period eleven maximin is the champion value"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The greatest element is the period-two repeating orbit, inherited from "
                            + "the shorter levels. What this level contributes is that none of "
                            + "its new classes beats it."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenMaximinE")),
            ]));
    }
}
