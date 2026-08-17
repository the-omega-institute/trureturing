using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class NoArbitrageRateUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two positive reversible exchange rates coincide exactly when neither cross-rate cycle "
        + "has multiplier above one.",
        H("No-Arbitrage Uniqueness of Reversible Rates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-arbitrage-uniqueness-of-reversible-rates"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/NoArbitrageRateUniqueness"
                    + ".no_arbitrage_iff_reversible_rates_eq"),
                H("No-arbitrage characterizes equality of reversible rates"),
                StatementSource.FromAuthor(NoArbitrageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rate1 and rate2 be positive real exchange rates. The two displayed "
                        + "quotients are the multipliers obtained by composing one proposed rate "
                        + "with the inverse of the other. Requiring both cycle multipliers to be "
                        + "at most one rules out gain in either direction.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle both identify div_le_one as the exact bridge "
                        + "from each quotient bound to an order comparison. Antisymmetry then "
                        + "forces equality. No exact combined no-arbitrage theorem was found. "
                        + "The local smart-search declaration-name query exited 1 with no hit; "
                        + "the LeanSearch API request returned HTTP 404 and is not counted as a "
                        + "negative search result.")),
                    Paragraph(Text(
                        "This closes the reversible-rate uniqueness sentence in pzg-v170 "
                        + "remark/27.612, atom "
                        + "pzg-residual-fa0e8ffc2bb3d31040f8eee2a35ffc3c1cbdc199c8bddf608bbd0da1c534cd85. "
                        + "The surrounding entropy, compression, and resource-economy analogies "
                        + "are not claimed as separate formal theorems."))),
                DescribeRole.Theorem))));

    private static Formula RateQuotient(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula NoArbitrageFormula()
    {
        Formula rate1 = F.Id("rate1");
        Formula rate2 = F.Id("rate2");

        return Disp(Seq(
            Forall, Sp, rate1, Comma, Sp, rate2, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
            Esc, D(0), Lt, rate1, Sp, Land, Sp, D(0), Lt, rate2, Sp, Rightarrow, Sp,
            Open,
            RateQuotient(rate1, rate2), Sp, Le, Sp, D(1), Sp, Land, Sp,
            RateQuotient(rate2, rate1), Sp, Le, Sp, D(1),
            Close, Sp, Leftrightarrow, Sp, rate1, Sp, Eq, Sp, rate2, Dot));
    }
}
