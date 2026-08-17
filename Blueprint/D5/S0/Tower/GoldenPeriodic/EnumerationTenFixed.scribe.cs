using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationTenFixedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var fixedCodes = Call("toFinset", Call("goldenFixedPointCodes", Num(10)));
        var expected = Id("goldenExpectedPointCodesTen");
        var decomposition = Equal(fixedCodes, expected);
        var blockCounts = Equal(
            Call("periodTenFixedBlockLengths"),
            Call("list", Num(21), Num(13), Num(21), Num(21),
                Num(13), Num(13), Num(8), Num(13)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The 123 period-ten fixed-point equations decompose into eight bounded blocks.",
            H("Period-Ten Fixed-Point Decomposition"),
            Blocks(
                Paragraph(Text(
                    "The legal three-step prefixes LLL, LLR, LRT, RTL, RTR, TLL, TLR, and TRT "
                        + "partition the symbolic equations. Each block is compared separately "
                        + "with the inherited and primitive orbit phases.")),
                Describe.Lean(
                    DescribeId.Create("period-ten-fixed-block-counts"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTenFixed."
                            + "golden_fixed_point_block_counts_ten"),
                    H("The eight fixed-point blocks are bounded"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(blockCounts)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The block sizes are 21, 13, 21, 21, 13, 13, 8, and 13; no arithmetic "
                            + "comparison expands more than twenty-one equations at once."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-ten-fixed-points-equal-orbit-phases"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationTenFixed."
                            + "golden_fixed_point_codes_ten_decompose"),
                    H("Every period-ten fixed point is an enumerated orbit phase"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(decomposition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "After the eight exact comparisons are recombined, the fixed-point "
                            + "codes are exactly the inherited divisor-period phases and the "
                            + "eleven new ten-cycles."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationTenData")),
            ]));
    }
}
