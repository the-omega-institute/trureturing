using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class AdmissibleCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary words with no two consecutive ones are counted by a Fibonacci number.",
        H("The Fibonacci Count of Zeckendorf-Admissible Words"),
        Blocks(
            new DocumentBlock.Section(H("Fixed-length zero words and weighted patterns"), Blocks(
                Paragraph(Text(
                    "At length three the admissible words are exactly 000, 100, 010, 001, and 101. Assigning "
                    + "weights two, three, and five to the three positions gives occupied sets empty, {2}, {3}, "
                    + "{5}, and {2,5}, with respective sums zero, two, three, five, and seven. The zero word is "
                    + "still a three-letter history, distinct from the empty word. Word length is retained by "
                    + "the Fin-indexed carrier and is not recovered from the occupied-weight sum.")),
                Paragraph(Text(
                    "The values at lengths zero and one are one and two, and wcount_succ_succ gives the "
                    + "recurrence a(n+2) = a(n+1)+a(n). Thus admissibleWord_card_eq_fib counts the complete "
                    + "fixed-length word set, including leading and trailing zeros.")))),
            new DocumentBlock.Section(H("Reconstruction from consecutive three-letter windows"), Blocks(
                Paragraph(Text(
                    "Let n+1 consecutive windows of width three be given, so at least one window is present. "
                    + "Suppose adjacent windows agree on their common two positions and each window has no "
                    + "adjacent ones. Their positions cover a word of length n+3. Any two overlapping windows "
                    + "have starting positions differing by at most two: equality on the overlap follows "
                    + "directly for neighboring windows and through the intervening window when the difference "
                    + "is two.")),
                Paragraph(Text(
                    "Gluing these functions on their position sets gives a unique word. Every adjacent pair "
                    + "of positions lies in one of the windows, so its two bits cannot both be one. This proves "
                    + "legality of the entire glued word. The support-covered gluing argument applies here with "
                    + "adjacent pairs as constraint supports.")),
                Paragraph(Text(
                    "A final window does not determine total length: for every n the all-zero word of length "
                    + "n+3 ends in the same three zeros. Different values of n give different complete words. A "
                    + "window records a local pattern, not an erased prefix or a free clock.")))),
            Describe.Lean(
                DescribeId.Create("zeckendorf-admissible-word-count-is-fibonacci"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/AdmissibleCount.admissibleWord_card_eq_fib"),
                H("The number of length-m admissible words is F(m+2)"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("card")), Sp,
                    Grp(F.Id("w"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("m"), Sp,
                    Rightarrow, Sp, F.Id("Bool"), Sp, Mid, Sp,
                    Operatorname, Grp(F.Id("Adm")), Sp, F.Id("m"), Sp, F.Id("w")), Sp,
                    Eq, Sp, F.Id("F"), Underscore, Grp(F.Id("m"), Plus, D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A binary word w of length m is Zeckendorf-admissible when it has no two "
                        + "consecutive true letters — the same no-consecutive-ones constraint that "
                        + "characterizes Zeckendorf representations. The number of such words of length "
                        + "m is exactly the Fibonacci number F(m+2), with the Mathlib convention "
                        + "F 0 = 0, F 1 = 1. Small cases: 1, 2, 3, 5, 8 for m = 0, 1, 2, 3, 4.")),
                    Paragraph(Text(
                        "The proof is a bijective recurrence. Splitting an admissible word of length "
                        + "m+2 on its first letter gives a bijection with the admissible words of length "
                        + "m+1 (when the first letter is false) and the admissible words of length m "
                        + "(when the first two letters are true then false — the second forced false by "
                        + "admissibility). Taking cardinalities yields the Fibonacci recurrence "
                        + "count(m+2) = count(m+1) + count(m), and a two-step induction closes it to "
                        + "F(m+2).")),
                    Paragraph(Text(
                        "The carrier retains every position of a fixed-length binary word. "
                        + "Identifying its cardinality with the dimension of another space requires "
                        + "an additional bijection or basis theorem for that space."))),
                DescribeRole.Theorem))));
}
