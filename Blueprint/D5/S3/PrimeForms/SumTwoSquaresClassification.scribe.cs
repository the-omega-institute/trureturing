using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class SumTwoSquaresClassificationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Grosswald =
        LibraryNoteRef.Create("D5/L/Arith/grosswald1985representations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/PrimeForms/SumTwoSquaresClassification",
            "A natural number is a sum of two squares exactly when every prime congruent"
            + " to three modulo four occurs to an even exponent in its factorization."),
        H("Classification of Sums of Two Squares"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("sum-of-two-squares-classification"),
                H("A natural number is a sum of two squares exactly when its prime factors"
                  + " congruent to three modulo four carry even exponents"),
                LeanTheorem(
                    "D5/S3/PrimeForms/SumTwoSquaresClassification."
                    + "eq_sq_add_sq_iff_even_factorization"),
                Disp(Seq(
                    Open, Exists, Sp, F.Id("a"), Comma, F.Id("b"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("n"), Eq, F.Id("a"), Caret, D(2), Plus, F.Id("b"), Caret, D(2),
                    Close, Quad, Leftrightarrow, Quad, Sp,
                    Forall, Sp, F.Id("q"), Esc, F.Text, Grp(F.Id("prime")), Comma, Esc,
                    F.Id("q"), Equiv, Sp, D(3), Esc,
                    Open, Operatorname, Grp(F.Id("mod")), Esc, D(4), Close,
                    Sp, Rightarrow, Sp,
                    D(2), Esc, Mid, Esc, F.Id("v"), Underscore, F.Id("q"),
                    Open, F.Id("n"), Close)),
                DescribeProvenance.LiteratureAttested(Grosswald),
                Blocks(Paragraph(Text(
                    "A natural number n is a sum of two natural squares if and only if "
                    + "every prime q congruent to three modulo four occurs to an even "
                    + "exponent in the factorization of n. The formal statement "
                    + "quantifies over all primes rather than only the prime factors of "
                    + "n: primes not dividing n, and every prime when n is zero, carry "
                    + "exponent zero, which is even, so the two readings agree and "
                    + "nothing is weakened. The proof is a thin honest wrapper over "
                    + "pinned Mathlib: the classification stated over the prime-factor "
                    + "support with the p-adic valuation is glued to the all-primes "
                    + "factorization form by discharging the out-of-support primes with "
                    + "the zero exponent. The source's proof route through descent at "
                    + "primes congruent to three modulo four, the representation of "
                    + "primes congruent to one modulo four, and the multiplicative "
                    + "composition identity is not attributed and is not reproved. "
                    + "Original numerical-certificate disposition: the source theorem is "
                    + "a purely universal biconditional and contains no numerical "
                    + "certificate.")))
            ))));
}
