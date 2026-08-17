using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSevenFixedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var generated = Call("toFinset", Call("tribonacciFixedPointCodes", Num(7)));
        var expected = Id("tribonacciExpectedPointCodesSeven");
        var decomposition = Equal(generated, expected);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The period-seven equations are exactly one inherited and seventy new phases.",
            H("Tribonacci Period-Seven Fixed Points"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("period-seven-equations-decompose-into-orbit-phases"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixed."
                            + "tribonacci_fixed_point_codes_seven_decompose"),
                    H("Period-seven equations decompose into certified orbit phases"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(decomposition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A seventy-one-cardinality squeeze turns the rotated itinerary "
                            + "inclusions into exact equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedB")),
            ]));
    }
}
