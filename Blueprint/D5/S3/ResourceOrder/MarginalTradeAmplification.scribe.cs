using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class MarginalTradeAmplificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marginal repricing amplifies marked value relative to the cash transferred by the trade.",
        H("Marginal Trade and Marked Value"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("marginal-trade-mark-amplification"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/MarginalTradeAmplification"
                    + ".marginal_trade_mark_amplification"),
                H("Marginal trade marked-value amplification"),
                StatementSource.FromAuthor(AmplificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let N be a nonnegative inventory, let the displayed price move from "
                        + "p0 to p1, and let a trade of size delta execute at average price pBar. "
                        + "The marked-value change is N(p1-p0), while the transferred cash is "
                        + "delta pBar.")),
                    Paragraph(Text(
                        "Substitution shows that the absolute marked-value change divided by "
                        + "traded cash is N times the absolute price move divided by delta pBar. "
                        + "The statement is an accounting identity and imposes no model of how "
                        + "the marginal price move is generated.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies abs_mul and abs_of_nonneg as the exact algebraic "
                        + "steps. Repository and pinned-library searches found no market-specific "
                        + "declaration for the complete ratio identity."))),
                DescribeRole.Theorem))));

    private static Formula AmplificationFormula()
    {
        Formula inventory = F.Id("N");
        Formula before = F.Id("p0");
        Formula after = F.Id("p1");
        Formula size = F.Id("delta");
        Formula average = F.Id("pBar");
        Formula marked = F.Id("markedChange");
        Formula cash = F.Id("tradeCash");
        Formula move = Seq(after, Sp, Minus, Sp, before);

        return Disp(Seq(
            D(0), Sp, Leq, Sp, inventory, Sp, Land, Sp,
            marked, Sp, Eq, Sp, inventory, Open, move, Close, Sp, Land, Sp,
            cash, Sp, Eq, Sp, size, Cdot, Sp, average, Sp, Rightarrow, Sp,
            Frac, Grp(Lvert, Sp, marked, Sp, Rvert), Grp(cash), Sp, Eq, Sp,
            Frac,
            Grp(inventory, Cdot, Sp, Lvert, Sp, move, Sp, Rvert),
            Grp(size, Cdot, Sp, average), Dot));
    }
}
