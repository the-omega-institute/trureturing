using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class PrimeFactorizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/PrimeFactorization",
            "Every natural number greater than one is a product of finitely many primes."),
        H("Existence of Prime Factorization"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("every-natural-above-one-is-a-product-of-primes"),
                H("Every natural number above one is a product of primes"),
                LeanTheorem(
                    "D5/S3/Arith/PrimeFactorization.exists_prime_factorization"),
                Disp(Seq(Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("n"), Gt, D(1), Sp, Rightarrow, Sp, Exists, Thin, Sp, F.Id("l"), Comma, Esc, Open, Forall, Sp, F.Id("p"), InMacro, Sp, F.Id("l"), Comma, Esc, F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Close, Sp, Land, Sp, Prod, Sp, F.Id("l"), Sp, Eq, Sp, F.Id("n"))),
                DescribeProvenance.LiteratureAttested(Apostol),
                Blocks(Paragraph(Text(
                    "Every natural number greater than one factors as a product of finitely "
                    + "many prime numbers. This is the existence half of the fundamental theorem "
                    + "of arithmetic (uniqueness is a separate statement). The formal claim fixes "
                    + "the natural-number carrier and exhibits an explicit finite list whose "
                    + "entries are all prime and whose product is the given number, so the "
                    + "hypothesis is a genuine bound and the conclusion a genuine existential, "
                    + "not a hollow or vacuous statement; since the product of the empty list is "
                    + "one, the bound n > 1 forces the witnessing list to be non-empty. The proof "
                    + "discharges the claim through Mathlib's prime-factors list, its all-prime "
                    + "membership lemma, and its product identity; the deposited atom asserts the "
                    + "truth of the statement, and the proof route may differ from the source's "
                    + "minimal-counterexample argument. Original numerical-certificate disposition: "
                    + "the source theorem is a purely existential factorization statement and "
                    + "contains no numerical certificate.")))
            ))));
}
