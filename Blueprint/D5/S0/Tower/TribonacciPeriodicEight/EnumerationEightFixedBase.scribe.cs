using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEight;

internal sealed class EnumerationEightFixedBaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var equations = Call("tribonacciFixedPointCodes", Num(8));
        var count = Equal(Call("length", equations), Num(131));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The period-eight generator has one hundred thirty-one closed equations.",
            H("Tribonacci Period-Eight Fixed-Point Base"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("one-hundred-thirty-one-period-eight-fixed-point-equations"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightFixedBase."
                            + "tribonacci_fixed_point_code_count_exactly_eight"),
                    H("One hundred thirty-one period-eight fixed-point equations"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(count)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The three closed-gap counts are eighty-one, thirteen, and thirty-seven; "
                            + "a shared multiplier lemma certifies the denominator."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSeven")),
            ]));
    }
}
