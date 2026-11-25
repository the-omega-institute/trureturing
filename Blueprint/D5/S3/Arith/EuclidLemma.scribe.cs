using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class EuclidLemmaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime dividing a product of two naturals divides one of the factors.",
        H("Euclid's Lemma on the Prime Axis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-dividing-a-product-divides-a-factor"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/EuclidLemma.euclid_prime_dvd_mul"),
                H("A prime dividing a product divides a factor"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("p"), Comma, F.Id("a"), Comma, F.Id("b"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Sp, Land, Sp, F.Id("p"), Sp, Mid, Sp, F.Id("a"), Cdot, Sp, F.Id("b"), Sp, Rightarrow, Sp, F.Id("p"), Sp, Mid, Sp, F.Id("a"), Sp, Lor, Sp, F.Id("p"), Sp, Mid, Sp, F.Id("b")))),
                AssessedProvenance.FromLiterature(Apostol),
                Blocks(Paragraph(Text(
                    "For natural numbers, a prime that divides a product divides at least one "
                    + "factor. This is the classical Euclid lemma and the first building block "
                    + "of the two-axis norm reading exemplar; the source volume derives it from "
                    + "the additivity of the prime-exponent valuation on the free commutative "
                    + "monoid of the prime axis. The proof reads Mathlib primality through the "
                    + "D5 divisor characterization. Since gcd(p,a) divides p, it equals one or "
                    + "p. In the first case Bézout's identity gives divisibility of b. In the "
                    + "second case p divides a."))),
                DescribeRole.Lemma))));
}
