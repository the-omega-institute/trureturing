using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSixFixedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var periodSixCodes = Call("tribonacciFixedPointCodes", Num(6));
        var equationCount = Equal(Call("length", periodSixCodes), Num(39));
        var expected = Id("tribonacciExpectedPointCodesSix");
        var decomposition = Equal(Call("toFinset", periodSixCodes), expected);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Thirty-nine period-six equations reduce to inherited phases and five new cycles.",
            H("Tribonacci Period-Six Fixed Points"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("thirty-nine-period-six-fixed-point-equations"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed."
                            + "tribonacci_fixed_point_code_count_exactly_six"),
                    H("Thirty-nine period-six fixed-point equations"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(equationCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The three-letter transition graph has thirty-nine closed, phase-marked "
                            + "words of length six."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-six-equations-decompose-into-certified-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSixFixed."
                            + "tribonacci_fixed_point_codes_six_decompose"),
                    H("Period-six equations decompose into certified orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(decomposition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Independent large, small, and combined gap checks identify all fixed "
                            + "codes with the inherited phases and thirty new phases."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint")),
            ]));
    }
}
