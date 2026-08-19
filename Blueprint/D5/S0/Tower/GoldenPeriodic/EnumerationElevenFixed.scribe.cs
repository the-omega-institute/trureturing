using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationElevenFixedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var fixedCodes = Call("toFinset", Call("goldenFixedPointCodes", Num(11)));
        var expected = Id("goldenExpectedPointCodesEleven");
        var decomposition = Equal(fixedCodes, expected);
        var blockCounts = Equal(
            Call("periodElevenFixedBlockLengths"),
            Call("list", Num(34), Num(21), Num(34), Num(34),
                Num(21), Num(21), Num(13), Num(21)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The 199 period-eleven fixed equations decompose into eight prefix blocks.",
            H("Period-Eleven Fixed-Point Decomposition"),
            Blocks(
                Paragraph(Text(
                    "The three 34-equation blocks are each refined into fourth-step subblocks "
                        + "of size twenty-one and thirteen before exact comparison.")),
                Describe.Lean(
                    DescribeId.Create("period-eleven-fixed-block-counts"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationElevenFixed."
                            + "golden_fixed_point_block_counts_eleven"),
                    H("The eight fixed-point blocks have exact sizes"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(blockCounts)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The block sizes are 34, 21, 34, 34, 21, 21, 13, and 21."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("period-eleven-fixed-points-equal-orbit-phases"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationElevenFixed."
                            + "golden_fixed_point_codes_eleven_decompose"),
                    H("Every period-eleven fixed point is an enumerated phase"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(decomposition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact fixed-point codes equal the inherited fixed phase and all "
                            + "198 phases on the primitive eleven-cycles."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationElevenSeparation")),
            ]));
    }
}
