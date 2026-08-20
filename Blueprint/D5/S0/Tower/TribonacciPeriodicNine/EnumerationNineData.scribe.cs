using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicNine;

internal sealed class EnumerationNineDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var orbit = Id("o");
        var orbits = Id("TribonacciCodedOrbit");
        var reps = Id("tribonacciPeriodNineOrbitRepresentatives");

        var statement = Equal(Call("length", reps), Num(26));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineData.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Twenty-six exact primitive period-nine Tribonacci orbit certificates.",
            H("Enumeration Nine Data"),
            Blocks(
                Paragraph(Text(
                    "The twenty-six words are the primitive rotation classes among the two "
                        + "hundred forty phase-marked solutions of the period-nine equations. "
                        + "The enumerator was validated against the frozen period-eight data "
                        + "before use: it reproduces one hundred thirty-one phase points and "
                        + "fifteen primitive classes, and those fifteen rotation classes "
                        + "coincide with the committed ones as sets.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-period-nine-representatives"),
                    DeclarationHandle.Create(declarationPrefix + "tribonacci_period_nine_representative_count"),
                    H("Enumeration Nine Data"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The count is the object-level claim: exactly twenty-six primitive "
                            + "rotation classes at period nine. Validity of each certificate is "
                            + "a separate statement in the companion module."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEight")),
            ]));
    }
}
