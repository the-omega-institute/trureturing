using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class LedgerLengthGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Analytic/LedgerLengthGrowth",
            "A positive generation strictly increases every additive real ledger length."),
        H("Positive Ledger-Length Growth"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("positive-generation-strictly-increases-ledger-length"),
                DescribeKind.Theorem,
                H("Positive generation strictly increases ledger length"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Analytic/LedgerLengthGrowth."
                    + "ledger_length_strict_mono_of_positive_generation")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "正生成之正性以 length u > 0 承载(素指数求和的具体形属素账本载体,另单);"
                    + "推论中\"逆账本/群化扩张\"属 open 账,留叙事层不入定理。"))),
                LatexStatement.Create(
                    @"$L(u)>0\quad\Rightarrow\quad L(a)<L(a+u)$")))));
}
