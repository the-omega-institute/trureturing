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
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("positive-generation-strictly-increases-ledger-length"),
                H("Positive generation strictly increases ledger length"),
                LeanTheorem(
                    "D5/S3/Analytic/LedgerLengthGrowth."
                    + "ledger_length_strict_mono_of_positive_generation"),
                new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("L")), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.GreaterThan), new Formula.LatexDigits([0]), new Formula.LatexMacro(FormulaLatexMacro.Quad), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexMacro(FormulaLatexMacro.Quad), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("L")), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.LessThan), new Formula.LatexWord(FormulaIdentifier.Create("L")), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "正生成之正性以 length u > 0 承载(素指数求和的具体形属素账本载体,另单);"
                    + "推论中\"逆账本/群化扩张\"属 open 账,留叙事层不入定理。")))
            ))));
}
