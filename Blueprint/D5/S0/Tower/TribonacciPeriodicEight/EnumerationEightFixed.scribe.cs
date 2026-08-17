using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEight;

internal sealed class EnumerationEightFixedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var generated = Call("toFinset", Call("tribonacciFixedPointCodes", Num(8)));
        var expected = Id("tribonacciExpectedPointCodesEight");
        var decomposition = Equal(generated, expected);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The period-eight equations are exactly eleven inherited and one hundred twenty new phases.",
            H("Tribonacci Period-Eight Fixed Points"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("period-eight-equations-decompose-into-orbit-phases"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixed."
                            + "tribonacci_fixed_point_codes_eight_decompose"),
                    H("Period-eight equations decompose into certified orbit phases"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(decomposition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A one hundred thirty-one-cardinality squeeze turns the inherited and "
                            + "rotated-itinerary inclusions into exact equality."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedB")),
            ]));
    }
}
