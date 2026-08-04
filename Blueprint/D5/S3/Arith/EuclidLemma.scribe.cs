using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class EuclidLemmaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/EuclidLemma",
            "A prime dividing a product of two naturals divides one of the factors."),
        H("Euclid's Lemma on the Prime Axis"),
        Blocks(
            DocumentBlock.Describe.Lemma(
                DescribeId.Create("prime-dividing-a-product-divides-a-factor"),
                H("A prime dividing a product divides a factor"),
                LeanTheorem(
                    "D5/S3/Arith/EuclidLemma.euclid_prime_dvd_mul"),
                Disp(Seq(Forall, Sp, F.Id("p"), Comma, F.Id("a"), Comma, F.Id("b"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Sp, Land, Sp, F.Id("p"), Sp, Mid, Sp, F.Id("a"), Cdot, Sp, F.Id("b"), Sp, Rightarrow, Sp, F.Id("p"), Sp, Mid, Sp, F.Id("a"), Sp, Lor, Sp, F.Id("p"), Sp, Mid, Sp, F.Id("b"))),
                DescribeProvenance.LiteratureAttested(Apostol),
                Blocks(Paragraph(Text(
                    "For natural numbers, a prime that divides a product divides at least one "
                    + "factor. This is the classical Euclid lemma and the first building block "
                    + "of the two-axis norm reading exemplar; the source volume derives it from "
                    + "the additivity of the prime-exponent valuation on the free commutative "
                    + "monoid of the prime axis. The formal statement fixes the natural-number "
                    + "carrier and the standard divisibility relation, so the hypothesis is "
                    + "genuine primality and a genuine product divisibility, not a hollow or "
                    + "vacuous premise. The proof discharges the claim through Mathlib's "
                    + "Nat.Prime.dvd_mul, which supplies the equivalence for a prime; the "
                    + "deposited atom asserts the truth of the statement, and the proof route "
                    + "may differ from the source's valuation-additivity derivation. Original "
                    + "numerical-certificate disposition: the source lemma is a purely logical "
                    + "divisibility implication and contains no numerical certificate.")))
            ))));
}
