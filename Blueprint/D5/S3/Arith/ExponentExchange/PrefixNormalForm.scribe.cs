using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ExponentExchange;

internal sealed class PrefixNormalFormDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef AlaogluErdos =
        LibraryNoteRef.Create("D5/L/Arith/alaoglu1944highly");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive integer has a companion no larger, with as many distinct primes and "
            + "non-increasing exponents, whose normalized divisor sum is at least as large.",
        H("Exponent Normal Form with the Same Number of Distinct Primes"),
        Blocks(Describe.Lean(
            DescribeId.Create("antitone-exponent-form"),
            DeclarationHandle.Create(
                "D5/S3/Arith/ExponentExchange/PrefixNormalForm.exists_antitone_exponent_form"),
            H("A no-larger integer with non-increasing exponents dominates sigma(n)/n"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(AlaogluErdos),
            Blocks(
                Paragraph(Text(
                    "For every natural number n at least 1 there is m with 1 <= m <= n, the same "
                        + "number of distinct prime factors as n (the cardinality of Nat.primeFactors), "
                        + "Nat.factorization m q <= Nat.factorization m p for all primes p < q, and "
                        + "sigma(1,n)/n <= sigma(1,m)/m in the real numbers. The exponent condition "
                        + "forces the support of m to be an initial segment of the primes: if q divides m "
                        + "then every smaller prime divides m.")),
                Paragraph(Text(
                    "The proof is strong induction on n. When the exponents already decrease, m = n. "
                        + "Otherwise there are primes p < q with smaller exponent at p, possibly zero, and "
                        + "the frozen exchange theorem IntegerSwap.prime_exponent_swap swaps the two "
                        + "exponents: the result is a smaller positive integer with a strictly larger "
                        + "normalized divisor sum. Writing the integer as t*p^a*q^b with t coprime to p*q, "
                        + "its number of distinct primes is that of t plus one for each nonzero exponent, "
                        + "so the swap keeps the count. The induction hypothesis applied to the smaller "
                        + "integer finishes.")),
                Paragraph(Text(
                    "Because the companion is no larger, e^gamma*log(log(m)) <= e^gamma*log(log(n)) "
                        + "whenever m > 1, so Robin's inequality at a companion m above 5040 implies it at "
                        + "n. The theorem therefore reduces Robin's inequality for integers with a bounded "
                        + "number of distinct primes to products of powers of the first primes with "
                        + "non-increasing exponents. The exchange argument is the one Alaoglu and Erdos use "
                        + "for superabundant numbers; here it is iterated on an arbitrary integer and keeps "
                        + "the number of distinct primes. The companion is not claimed to be unique or "
                        + "to maximize sigma(1,m)/m among integers up to n."))),
            DescribeRole.Theorem))));
}
