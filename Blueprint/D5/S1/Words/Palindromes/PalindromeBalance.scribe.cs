using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class PalindromeBalanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even-length palindrome has zero alternating sum.",
        H("Balance of an Even Palindrome"),
        Blocks(
            Paragraph(Text(
                "This document closes only the even-palindrome balance sentence in residual "
                    + "remark 27.330. It does not formalize the trace formula, drift formula, "
                    + "or the converse claim that balance need not imply palindromicity.")),
            Describe.Lean(
                DescribeId.Create("even-palindrome-alternating-sum-vanishes"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Palindromes/PalindromeBalance."
                        + "even_palindrome_alternating_sum_eq_zero"),
                H("An even palindrome is alternatingly balanced"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("w"), InMacro,
                    Operatorname, Grp(F.Id("List")), Open, Mathbb, Grp(F.Id("Z")), Close,
                    Comma, Esc, Operatorname, Grp(F.Id("Palindrome")), Open, F.Id("w"), Close,
                    Sp, Land, Sp, Operatorname, Grp(F.Id("even")), Open,
                    Operatorname, Grp(F.Id("length")), Open, F.Id("w"), Close, Close,
                    Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("alternatingSum")), Open,
                    F.Id("w"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's alternating-sum reversal law changes the sign when the list has "
                        + "even length. Palindromicity identifies the reversed list with the "
                        + "original list, so the integer alternating sum equals its own negative "
                        + "and therefore vanishes."))),
                DescribeRole.Theorem)),
        []));
}
