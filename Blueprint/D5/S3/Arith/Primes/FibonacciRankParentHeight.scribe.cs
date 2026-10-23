using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciRankParentHeightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/FibonacciRankParentHeight.";
    private static readonly LibraryNoteRef LucaTron =
        LibraryNoteRef.Create("D5/L/Factorization/lucatron2015selffibonacci");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Following prime factors of Fibonacci entry ranks from any prime reaches 2, 3 or 5, and "
            + "every such path from p has at most log2(p - 1) steps.",
        H("Height of the Fibonacci rank-parent recursion"),
        Blocks(
            Paragraph(Text(
                "For a prime p, the Fibonacci entry rank z(p) is the least positive index r with "
                    + "p dividing F_r. A rank-parent edge leads from a prime p > 5 to a prime "
                    + "factor of z(p). The roots 2, 3 and 5 are the first prime Fibonacci "
                    + "numbers; rank-parent edges leaving them are not followed, since "
                    + "z(2) = 3, z(3) = 4 and z(5) = 5 only cycle among the roots.")),
            Describe.Lean(
                DescribeId.Create("rank-descent"),
                DeclarationHandle.Create(Prefix + "RankDescent"),
                H("Rank-parent paths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "RankDescent p r k states that k rank-parent edges lead from the prime p to "
                        + "the prime r. Each edge starts at a prime above 5 and ends at a prime "
                        + "factor of the starting prime's entry rank; different parent choices "
                        + "give different paths."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rank-parent-halving"),
                DeclarationHandle.Create(Prefix + "two_mul_le_of_dvd_fibonacciRank"),
                H("A rank parent is at most half of p + 1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LucaTron),
                Blocks(
                    Paragraph(Text(
                        "For primes p > 5 and q with q dividing z(p), 2q <= p + 1.")),
                    Paragraph(Text(
                        "The frozen rank bound gives z(p) dividing p - 1 when (5/p) = 1 and p + 1 "
                            + "otherwise; both numbers are even because p is odd. A parent q = 2 "
                            + "satisfies 4 <= p + 1. An odd parent is coprime to 2, so 2q divides "
                            + "the even number and is at most p + 1. Luca and Tron use the "
                            + "strict decrease of prime factors of entry ranks; the bound here "
                            + "records the factor two that this descent loses at every step."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rank-descent-root-and-height"),
                DeclarationHandle.Create(Prefix + "rankDescent_to_root_and_height"),
                H("Every prime reaches a root within log2(p - 1) steps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LucaTron),
                Blocks(
                    Paragraph(Text(
                        "For every prime p there is a rank-parent path from p to a prime r <= 5, "
                            + "that is to 2, 3 or 5; and every rank-parent path from p, along any "
                            + "choice of parents, has k edges with 2^k <= p - 1.")),
                    Paragraph(Text(
                        "Existence is a strong induction on p: z(p) is not 1 because F_1 = 1, so "
                            + "its least prime factor is a parent, and the halving bound makes "
                            + "that parent smaller than p. The length bound is an induction on "
                            + "the path: each edge from p to q gives 2(q - 1) <= p - 1, so the "
                            + "factor 2^k is paid along the path and the root still satisfies "
                            + "1 <= r - 1.")),
                    Paragraph(Text(
                        "The recursion records divisibility of Fibonacci numbers, which classifies "
                            + "each prime by (5/p) and its rank. It does not record the size "
                            + "distribution of primes in intervals, so it gives no estimate of "
                            + "prime sums such as those controlling Robin's inequality."))),
                DescribeRole.Theorem))));
}
