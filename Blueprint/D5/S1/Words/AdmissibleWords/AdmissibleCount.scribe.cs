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
                        "Only this counting clause is recorded here. The identification of the count "
                        + "with the dimension of a Fibonacci-anyon fusion space, the coprimality of "
                        + "consecutive Fibonacci numbers, and the wider observer-algebra content of the "
                        + "source are not covered by this statement."))),
                DescribeRole.Theorem))));
}
