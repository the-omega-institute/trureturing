using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSevenFixedBaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var equations = Call("tribonacciFixedPointCodes", Num(7));
        var count = Equal(Call("length", equations), Num(71));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The period-seven generator has seventy-one closed equations.",
            H("Tribonacci Period-Seven Fixed-Point Base"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("seventy-one-period-seven-fixed-point-equations"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenFixedBase."
                            + "tribonacci_fixed_point_code_count_exactly_seven"),
                    H("Seventy-one period-seven fixed-point equations"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(count)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A structural multiplier lemma reduces every length-seven "
                            + "denominator to one exact cubic norm computation."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint")),
            ]));
    }
}
