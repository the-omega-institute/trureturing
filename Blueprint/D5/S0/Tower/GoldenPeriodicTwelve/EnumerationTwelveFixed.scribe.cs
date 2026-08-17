using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodicTwelve;

internal sealed class EnumerationTwelveFixedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var fixedCodes = Call("goldenFixedPointCodes", Num(12));
        var count = Equal(Call("length", fixedCodes), Num(322));
        var decomposition = Equal(
            Call("toFinset", fixedCodes),
            Id("goldenExpectedPointCodesTwelve"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The 322 period-twelve fixed equations decompose into 21 prefix blocks.",
            H("Period-Twelve Fixed-Point Decomposition"),
            Blocks(
                Paragraph(Text(
                    "Every block contains only eight, thirteen, or twenty-one exact affine "
                        + "fixed equations.")),
                Describe.Lean(
                    DescribeId.Create("three-hundred-twenty-two-period-twelve-fixed-codes"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed."
                            + "golden_fixed_point_code_count_exactly_twelve"),
                    H("There are exactly 322 period-twelve fixed codes"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(count)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The twenty-one prefix-block counts sum exactly to 322."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-twelve-fixed-points-equal-orbit-phases"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveFixed."
                            + "golden_fixed_point_codes_twelve_decompose"),
                    H("Every period-twelve fixed point is an enumerated phase"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(decomposition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact fixed-point codes equal all inherited phases and all 300 "
                            + "phases on the primitive twelve-cycles."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveSeparation")),
            ]));
    }
}
