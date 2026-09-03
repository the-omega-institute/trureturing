using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class ZeckendorfGoldenBetaGapBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least Zeckendorf digit selects the long or short consecutive golden Euler-layer step.",
        H("Zeckendorf Golden Beta Gap Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorf-selects-golden-beta-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/EulerGerm/ZeckendorfGoldenBetaGapBridge."
                    + "zeckendorf_selects_golden_beta_gap"),
                H("The least digit selects the next golden beta gap"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("v"), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak,
                    Open,
                    Neg, Open, D(2), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("v"), Close, Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("beta")), Open, F.Id("v+1"), Close,
                    Minus, Operatorname, Grp(F.Id("beta")), Open, F.Id("v"), Close,
                    Sp, Eq, Sp, Varphi, Caret, Grp(D(2)),
                    Close,
                    Sp, Land, RowBreak,
                    Open,
                    D(2), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("v"), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("beta")), Open, F.Id("v+1"), Close,
                    Minus, Operatorname, Grp(F.Id("beta")), Open, F.Id("v"), Close,
                    Sp, Eq, Sp, Varphi,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Absence of Fibonacci index two in the canonical Zeckendorf address gives the long phi-squared gap; presence gives the short phi gap.")),
                    Paragraph(Text(
                        "The proof composes the existing Zeckendorf-Beatty bridge with the all-order golden beta-gap dichotomy. It records a layer transition code and does not claim that Zeckendorf encodes prime, phase, or continuous-scale coordinates."))),
                DescribeRole.Theorem))));
}
