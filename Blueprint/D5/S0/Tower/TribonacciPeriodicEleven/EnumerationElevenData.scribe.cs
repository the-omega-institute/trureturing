using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEleven;

internal sealed class EnumerationElevenDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var orbit = Id("o");
        var orbits = Id("TribonacciCodedOrbit");
        var reps = Id("tribonacciPeriodElevenOrbitRepresentatives");

        var statement = Equal(Call("length", reps), Num(74));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicEleven/EnumerationElevenData.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Period-eleven Tribonacci certificates, part Data.",
            H("Enumeration Eleven Data"),
            Blocks(
                Paragraph(Text(
                    "The enumerator was calibrated against all three committed levels before "
                        + "use, and against their rotation classes as sets rather than their "
                        + "counts: it reproduces the fifteen, twenty-six and forty-two classes "
                        + "exactly.")),
                Describe.Lean(
                    DescribeId.Create("the-period-eleven-enumeration-lists-seventy-four"),
                    DeclarationHandle.Create(declarationPrefix + "tribonacci_period_eleven_representative_count"),
                    H("Enumeration Eleven Data"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The left and right branch split of the arm minimum was measured for "
                            + "this level: thirty-nine left and thirty-five right. It differs at "
                            + "every level, so the shorter levels' sets are not reusable."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenMaximinC")),
            ]));
    }
}
