using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class PalindromeMiddleParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd-length palindrome decomposes around a middle entry that determines its sum parity.",
        H("Middle Parity of an Odd Palindrome"),
        Blocks(
            Paragraph(Text(
                "This document closes only the palindrome lemma in residual appendix E.107. "
                    + "It does not formalize the subsequent Pell or Rademacher claims.")),
            Describe.Lean(
                DescribeId.Create("odd-palindrome-sum-parity-is-middle-parity"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Palindromes/PalindromeMiddleParity."
                        + "odd_palindrome_sum_mod_two_eq_middle"),
                H("The middle entry determines the sum parity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("w"), InMacro,
                    Operatorname, Grp(F.Id("List")), Open, Mathbb, Grp(F.Id("N")), Close,
                    Comma, Esc, Operatorname, Grp(F.Id("Palindrome")), Open, F.Id("w"), Close,
                    Sp, Land, Sp, Operatorname, Grp(F.Id("odd")), Open,
                    Operatorname, Grp(F.Id("length")), Open, F.Id("w"), Close, Close,
                    Sp, Rightarrow, Sp, Exists, Sp, F.Id("u"), Comma, F.Id("m"), Comma, Esc,
                    F.Id("w"), Sp, Eq, Sp, Operatorname, Grp(F.Id("append")), Open,
                    F.Id("u"), Comma, OpenBracket, F.Id("m"), CloseBracket, Comma,
                    Operatorname, Grp(F.Id("reverse")), Open, F.Id("u"), Close, Close,
                    Sp, Land, Sp, Operatorname, Grp(F.Id("mod")), Open,
                    Operatorname, Grp(F.Id("sum")), Open, F.Id("w"), Close, Comma, D(2), Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("mod")), Open, F.Id("m"), Comma, D(2), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Palindrome induction removes matching endpoints in pairs. Odd length leaves "
                        + "one middle entry, and every removed pair contributes an even amount to "
                        + "the natural-number sum."))),
                DescribeRole.Theorem)),
        []));
}
