using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class SumTwoSquaresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/PrimeForms/SumTwoSquares",
            "A prime congruent to one modulo four is a sum of two natural squares."),
        H("Prime Representation as a Sum of Two Squares"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("prime-congruent-to-one-is-a-sum-of-two-squares"),
                H("A prime congruent to one modulo four is a sum of two squares"),
                LeanTheorem(
                    "D5/S3/PrimeForms/SumTwoSquares."
                    + "prime_eq_sq_add_sq_of_mod_four_eq_one"),
                LatexStatement.Create(
                    @"$$p\ \text{prime}\ \land\ p\equiv 1\ (\operatorname{mod}\ 4)"
                    + @"\quad\Rightarrow\quad "
                    + @"\exists a,b\in\mathbb{N},\ p=a^2+b^2$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every natural prime p whose remainder modulo four is one, there are "
                    + "natural numbers a and b such that p equals a squared plus b squared. "
                    + "The formal statement retains both the primality and congruence premises "
                    + "and asserts only existence, without adding positivity or uniqueness of "
                    + "the witnesses. The proof installs the explicit primality hypothesis as "
                    + "the local fact required by Mathlib, specializes the standard sum-of-two-"
                    + "squares result after excluding remainder three, and reverses its final "
                    + "equality. No numerical certificate is asserted.")))
            ))));
}
