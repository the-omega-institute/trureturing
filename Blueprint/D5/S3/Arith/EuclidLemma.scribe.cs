using static StrataLint.Scribe.DefinitionDsl;

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
            new DocumentBlock.Describe(
                DescribeId.Create("prime-dividing-a-product-divides-a-factor"),
                DescribeKind.Lemma,
                H("A prime dividing a product divides a factor"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Arith/EuclidLemma.euclid_prime_dvd_mul")),
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
                    + "divisibility implication and contains no numerical certificate."))),
                LatexStatement.Create(
                    @"$$\forall p,a,b\in\mathbb{N},\ p\ \text{prime} \land p \mid a\cdot b "
                    + @"\Rightarrow p \mid a \lor p \mid b$$")))));
}
