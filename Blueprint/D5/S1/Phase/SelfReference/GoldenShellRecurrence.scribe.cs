using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.SelfReference;

internal sealed class GoldenShellRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden shell s(n)=floor((n+1)/phi) satisfies the Hofstadter G recurrence s(n)=n-s(s(n-1)).",
        H("The Golden Shell Hofstadter Recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-shell-satisfies-hofstadter-g-recurrence"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/SelfReference/GoldenShellRecurrence.golden_shell_recurrence"),
                H("The golden shell satisfies the Hofstadter G self-referential recurrence"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("s"), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    Lfloor, Frac, Grp(F.Id("n"), Plus, D(1)), Grp(Phi), Rfloor, RowBreak,
                    F.Id("s"), Open, F.Id("n"), Close, Sp, Eq, Sp,
                    F.Id("n"), Minus, F.Id("s"), Open, F.Id("s"), Open, F.Id("n"), Minus, D(1), Close, Close,
                    Qquad, Open, F.Id("n"), Ge, D(1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the golden shell function s(n) = floor((n+1)/phi) — the Zeckendorf/Beatty golden "
                        + "shift with slope 1/phi (approximately 0.618, not phi itself) — the theorem proves the "
                        + "Hofstadter G self-referential recurrence s(n) = n - s(s(n-1)) for every n >= 1, "
                        + "equivalently the additive core s(m+1) + s(s(m)) = m+1. Thus the ledger's golden shift "
                        + "and Douglas Hofstadter's self-referential G sequence (OEIS A005206) are the same "
                        + "function.")),
                    Paragraph(Text(
                        "The recurrence reduces to the additive core. Writing tau = 1/phi = phi - 1 (so "
                        + "tau^2 = 1 - tau and tau*(1+tau) = 1), the real value x = (m+1)*tau has floor A = s(m). "
                        + "The fractional part f = x - A is never exactly tau^2 (because (m+2)*tau is irrational), "
                        + "so a case split on f < tau^2 versus f > tau^2 evaluates both nested floors, "
                        + "floor(x + tau) = s(m+1) and floor((A+1)*tau) = s(s(m)), via floor bracket bounds; in "
                        + "each branch the two contributions cancel exactly to m+1.")),
                    Paragraph(Text(
                        "Mathlib supplies the golden ratio and floor arithmetic but no Hofstadter G recurrence, "
                        + "so this is a genuine construction rather than a library restatement; it also upgrades "
                        + "the source observation's numerical check (no exception for n <= 10^5) to a proof for "
                        + "all n. Only this G-identity (part one of the observation) is recorded; the separate MIU "
                        + "invariant (part two, that the reachable theorem strings have I-number congruent to 1 or "
                        + "2 modulo 3) is not covered."))),
                DescribeRole.Theorem
            )),
        []));
}
