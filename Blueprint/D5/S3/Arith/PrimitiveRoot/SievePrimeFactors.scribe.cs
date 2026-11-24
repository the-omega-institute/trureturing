using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrimitiveRootSievePrimeFactorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered prime supports for the character sieve",
        H("Ordered prime supports for the character sieve"), Blocks(
            Describe.Lean(DescribeId.Create("nth-prime-successor"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_succ_le_of_prime"),
                H("Successor ranks below a prime"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "If the k-th prime is less than a prime p, the next prime is at most p. "
                    + "This successor step supports the lower bound for sorted prime lists."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nth-prime-sorted-list"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_le_get"),
                H("Prime ranks in a sorted list"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For any strictly increasing list of primes, its entry at index i is at "
                    + "least the i-th prime. The statement covers every index below the list "
                    + "length."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nth-prime-five"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_five"),
                H("The prime at index five"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "With zero-based indexing, the prime at index five is 13."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nth-prime-six"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_six"),
                H("The prime at index six"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "With zero-based indexing, the prime at index six is 17."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nth-prime-seven"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.nth_prime_seven"),
                H("The prime at index seven"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "With zero-based indexing, the prime at index seven is 19."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("first-eight-primes"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.firstEight"),
                H("The first eight primes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The ordered list is 2, 3, 5, 7, 11, 13, 17, 19. It supplies the rank "
                    + "bounds used in the radical estimate."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-rank-lower"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.prime_rank_lower"),
                H("Lower bounds at the first eight prime ranks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "At a position i below eight in a finite sequence q, assume only that q "
                    + "is strictly increasing on the prefix through i and that the entries on "
                    + "this prefix are prime. Then q(i) is at least the i-th entry of the "
                    + "first-eight list. No condition is imposed on entries after i. The "
                    + "proof applies the general sorted-list prime bound to this finite prefix."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("first-eight-lower"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.first_eight_le"),
                H("Coordinatewise lower bounds for eight primes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "An increasing prime sequence of length eight dominates the first-eight "
                    + "list. This specialization supplies the initial eight factors in the "
                    + "radical estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("geometric-radical-lower"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.radical_lower"),
                H("A geometric radical lower bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "If a natural number n has at least 8+m distinct prime factors, then "
                    + "9699690 times 19 to the power m is at most the product of its distinct "
                    + "prime factors. The first eight dominate the first-eight list, and "
                    + "every tail factor is at least 19. Arbitrary factor multiplicities "
                    + "are allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reciprocal-prime-tail"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_bound"),
                H("A reciprocal bound for the prime tail"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Let r be at least two and s at most six. A sequence q of length r+s "
                    + "needs to be strictly increasing and prime only on its first s+2 "
                    + "entries. Assume also that each suffix entry q(r+i) is at least q(i+2). "
                    + "Then the reciprocal suffix sum is bounded by the sum of reciprocals of "
                    + "the s entries starting at index two of the first-eight list. No other "
                    + "ordering or primality condition on the suffix is needed. The bound "
                    + "retains its dependence on s."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reciprocal-margin-five"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_five"),
                H("Margin for at most five tail primes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Under the prefix and suffix comparison assumptions of reciprocal_tail_bound, "
                    + "at most five tail primes leave 1 minus their reciprocal sum at least "
                    + "36628/85085. This general bound is consumed by both threshold proofs; "
                    + "the fixed arithmetic checks occur inside its proof."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reciprocal-margin-six"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SievePrimeFactors.reciprocal_tail_margin_six"),
                H("Margin for six tail primes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "With six tail primes and the same prefix and suffix comparisons, "
                    + "1 minus their reciprocal sum is at least 610847/1616615. The "
                    + "unbounded threshold argument uses this lower bound for its sieve margin."))),
                DescribeRole.Theorem))));
}
