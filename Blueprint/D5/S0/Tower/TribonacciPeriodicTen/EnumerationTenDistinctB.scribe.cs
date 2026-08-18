using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicTen;

internal sealed class EnumerationTenDistinctBDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var first = Call("flatMap", Id("orbitStates"), Id("tribonacciPeriodTenOrbitsThird"));
        var second = Call("flatMap", Id("orbitStates"), Id("tribonacciPeriodTenOrbitsSeventh"));

        var statement = Call("Disjoint", first, second);

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenDistinctB.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Period-ten phase codes have no duplicates inside a group and no overlap between "
                + "two groups.",
            H("Enumeration Ten Distinct B"),
            Blocks(
                Paragraph(Text(
                    "Forty-five statements across two modules: nine saying the codes inside a "
                        + "group of five are distinct, and thirty-six saying two different "
                        + "groups share no code. Grouping by five is forced by normalisation "
                        + "cost, not chosen for style.")),
                Describe.Lean(
                    DescribeId.Create("period-ten-third-and-seventh-groups-share-no-code"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_period_ten_third_seventh_state_codes_disjoint"),
                    H("Two period-ten groups share no code"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Assembling the components into a single statement over the whole list "
                            + "is not done here, for the same reason it was left at period nine, "
                            + "and remains open."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenData")),
            ]));
    }
}
