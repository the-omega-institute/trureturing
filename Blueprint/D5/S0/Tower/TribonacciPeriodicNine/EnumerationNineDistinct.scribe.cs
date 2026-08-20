using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicNine;

internal sealed class EnumerationNineDistinctDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var first = Call("flatMap", Id("orbitStates"), Id("tribonacciPeriodNineOrbitsFirst"));
        var second = Call("flatMap", Id("orbitStates"), Id("tribonacciPeriodNineOrbitsSecond"));

        var statement = Call("Disjoint", first, second);

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineDistinct.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Period-nine phase codes have no duplicates inside a group of five and no overlap "
                + "between groups.",
            H("Enumeration Nine Distinct"),
            Blocks(
                Paragraph(Text(
                    "Twenty-one statements: six saying the codes inside a group of five are "
                        + "distinct, and fifteen saying two different groups share no code. "
                        + "Grouping is forced by normalisation cost, which is also why the "
                        + "period-eight file groups by five.")),
                Describe.Lean(
                    DescribeId.Create("period-nine-first-and-second-groups-share-no-code"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_period_nine_first_second_state_codes_disjoint"),
                    H("The first two groups share no code"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Assembling the twenty-one components into a single statement over the "
                            + "whole representative list is not done here. The components carry "
                            + "the content; the assembly is bookkeeping and remains open."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineData")),
            ]));
    }
}
