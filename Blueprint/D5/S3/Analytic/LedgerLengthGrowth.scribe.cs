using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class LedgerLengthGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive generation strictly increases every additive real ledger length.",
        H("Positive Ledger-Length Growth"),
        Blocks(
                        Describe.Lean(
                DescribeId.Create("positive-generation-strictly-increases-ledger-length"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/LedgerLengthGrowth.ledger_length_strict_mono_of_positive_generation"),
                H("Positive generation strictly increases ledger length"),
                StatementSource.FromAuthor(In(Seq(F.Id("L"), Open, F.Id("u"), Close, Gt, D(0), Quad, Rightarrow, Quad, Sp, F.Id("L"), Open, F.Id("a"), Close, Lt, F.Id("L"), Open, F.Id("a"), Plus, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "正生成之正性以 length u > 0 承载(素指数求和的具体形属素账本载体,另单);"
                    + "推论中\"逆账本/群化扩张\"属 open 账,留叙事层不入定理。"))),
                DescribeRole.Theorem))));
}
