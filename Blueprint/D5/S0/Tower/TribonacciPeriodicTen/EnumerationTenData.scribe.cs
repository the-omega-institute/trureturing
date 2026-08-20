using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicTen;

internal sealed class EnumerationTenDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var orbit = Id("o");
        var orbits = Id("TribonacciCodedOrbit");
        var reps = Id("tribonacciPeriodTenOrbitRepresentatives");

        var statement = Equal(Call("length", reps), Num(42));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciPeriodicTen/EnumerationTenData.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Forty-two exact primitive period-ten orbit certificates.",
            H("Enumeration Ten Data"),
            Blocks(
                Paragraph(Text(
                    "The enumerator was calibrated against both committed levels before use, "
                        + "and against their rotation classes as sets rather than their counts: "
                        + "it reproduces the fifteen period-eight classes and the twenty-six "
                        + "period-nine classes exactly.")),
                Describe.Lean(
                    DescribeId.Create("the-period-ten-enumeration-lists-forty-two"),
                    DeclarationHandle.Create(declarationPrefix + "tribonacci_period_ten_representative_count"),
                    H("Enumeration Ten Data"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Names are numeric because forty-two exceeds the twenty-six letters the shorter levels used."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicNine/EnumerationNineMaximinB")),
            ]));
    }
}
