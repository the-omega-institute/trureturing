using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class LiquidityReserveBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonincreasing price curve has nonnegative liquidity reserve.",
        H("Liquidity Reserve Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("liquidity-reserve-nonnegative"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/LiquidityReserveBound"
                    + ".liquidity_reserve_nonnegative"),
                H("Liquidity reserve is nonnegative"),
                StatementSource.FromAuthor(LiquidityReserveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be a nonincreasing real price curve and let Q be nonnegative. "
                        + "The accumulated liquidity cost is the integral of P from zero to Q. "
                        + "It is bounded above by the rectangle with height P(0) and width Q.")),
                    Paragraph(Text(
                        "Subtracting the cost from that rectangle gives exactly the integral "
                        + "of the pointwise price drop P(0) - P(x). Consequently the liquidity "
                        + "reserve is nonnegative.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle both return "
                        + "intervalIntegral.integral_mono_on as the exact comparison theorem. "
                        + "The proof also directly uses Antitone.intervalIntegrable, the constant "
                        + "integral identity, and intervalIntegral.integral_sub. Repository "
                        + "searches found no equivalent D5 theorem. The LeanSearch API request "
                        + "failed and is not counted as a negative result.")),
                    Paragraph(Text(
                        "This closes qdo-v1 theorem/34.10, atom "
                        + "qdo-residual-c4eed44a7868133a4d15c1221a52a0a7e225b81ce63bc7f17699df5aa898b14b."))),
                DescribeRole.Theorem))));

    private static Formula LiquidityReserveFormula()
    {
        Formula p = F.Id("P");
        Formula q = F.Id("Q");
        Formula x = F.Id("x");
        Formula pAtZero = Call("P", D(0));
        Formula pAtX = Call("P", x);
        Formula cost = DefiniteIntegral(pAtX, q, x);
        Formula reserve = Seq(pAtZero, Cdot, Sp, q, Sp, Minus, Sp, cost);

        return Disp(Seq(
            Forall, Sp, p, Colon, Sp, Mathbb, Grp(F.Id("R")), To,
            Mathbb, Grp(F.Id("R")), Comma, Sp,
            q, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
            Operatorname, Grp(F.Id("Antitone")), Open, p, Close, Sp, Land, Sp,
            D(0), Leq, Sp, q, Sp, Rightarrow, Sp,
            cost, Sp, Leq, Sp, pAtZero, Cdot, Sp, q, Sp, Land, Sp,
            reserve, Sp, Eq, Sp,
            DefiniteIntegral(Seq(pAtZero, Sp, Minus, Sp, pAtX), q, x), Sp, Land, Sp,
            D(0), Leq, Sp, reserve, Dot));
    }

    private static Formula DefiniteIntegral(Formula integrand, Formula upper, Formula variable) =>
        Seq(Int, Underscore, Grp(D(0)), Caret, Grp(upper),
            Open, integrand, Close, Sp,
            F.Id("d"), variable);
}
