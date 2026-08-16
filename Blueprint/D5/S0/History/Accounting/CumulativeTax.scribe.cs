using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Accounting;

internal sealed class CumulativeTaxDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stepwise additive taxes accumulate to the terminal balance.",
        H("Cumulative Tax Accounting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stepwise-taxes-accumulate-to-the-terminal-balance"),
                DeclarationHandle.Create(
                    "D5/S0/History/Accounting/CumulativeTax.terminal_balance_eq_initial_add_tax"),
                H("Stepwise taxes accumulate to the terminal balance"),
                StatementSource.FromAuthor(CumulativeTaxFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S and tau be sequences in a commutative additive group. If each "
                            + "successive balance is the preceding balance plus the tax at that "
                            + "step, then the balance at time n is the initial balance plus the "
                            + "sum of all taxes at times strictly before n.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle supplied Finset.sum_range_sub. The Lean proof "
                            + "rewrites each tax as a consecutive balance difference and applies "
                            + "that upstream telescoping lemma directly."))),
                DescribeRole.Theorem))));

    private static Formula CumulativeTaxFormula()
    {
        Formula i = F.Id("i");
        Formula n = F.Id("n");
        Formula balance = F.Id("S");
        Formula tax = F.Id("tau");
        Formula balanceI = new Formula.Subscript(balance, i);
        Formula balanceSucc = new Formula.Subscript(balance, Seq(i, Plus, D(1)));
        Formula taxI = new Formula.Subscript(tax, i);
        Formula balanceN = new Formula.Subscript(balance, n);
        Formula balanceZero = new Formula.Subscript(balance, D(0));
        Formula taxSum = Seq(Sum, Underscore, Grp(i, Lt, Sp, n), Sp, taxI);

        return Disp(Seq(
            Open, Forall, Sp, i, Comma, Sp,
            balanceSucc, Sp, Eq, Sp, balanceI, Sp, Plus, Sp, taxI, Close,
            Sp, Rightarrow, Sp,
            balanceN, Sp, Eq, Sp, balanceZero, Sp, Plus, Sp, taxSum, Dot));
    }
}
