using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FiniteFibonacciRankClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/FiniteFibonacciRankClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime support of Fibonacci entry ranks has a bounded least closure over every "
            + "finite set of primes greater than five.",
        H("Finite Fibonacci rank closure"),
        Blocks(
            Paragraph(Text(
                "For a prime p, its Fibonacci entry rank is the least positive index r for "
                    + "which p divides F_r. The first-entry divisibility theorem and the "
                    + "golden Frobenius zero supply this rank. The construction below follows "
                    + "prime factors of these actual ranks.")),
            Describe.Lean(
                DescribeId.Create("fibonacci-rank-witness"),
                DeclarationHandle.Create(Prefix + "rankWitness"),
                H("Least positive zero witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each prime p, this witness gives a positive index r with p "
                        + "dividing F_r, together with a proof that every other positive "
                        + "zero index is at least r."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibonacci-entry-rank"),
                DeclarationHandle.Create(Prefix + "fibonacciRank"),
                H("The original entry rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a prime p, this value is the least positive r with p dividing F_r. "
                        + "Its value at a nonprime input is one, so it contributes no prime "
                        + "factors to the closure operation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rank-closure-seed"),
                DeclarationHandle.Create(Prefix + "rankClosureSeed"),
                H("Initial prime set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The initial set consists of the prescribed finite set together with "
                        + "the primes two, three and five."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rank-closure-step"),
                DeclarationHandle.Create(Prefix + "rankClosureStep"),
                H("Prime-support expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One step retains each current prime and adjoins every prime divisor "
                        + "of its Fibonacci entry rank."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibonacci-rank-closure"),
                DeclarationHandle.Create(Prefix + "fibonacciRankClosure"),
                H("Iterated closure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let B be the larger of five and the largest member of the prescribed "
                        + "set. Starting from the initial set, apply the expansion once per "
                        + "prime at most B. This gives a finite, explicitly determined set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-fibonacci-rank-closure"),
                DeclarationHandle.Create(Prefix + "finite_fibonacci_rank_closure"),
                H("Bounded least closure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite set S of primes greater than five, the iterated "
                        + "closure contains S and the three small primes, contains only "
                        + "primes at most B, and is unchanged by one further expansion. "
                        + "It is contained in every expansion-closed finite set that "
                        + "contains the same initial primes. Indeed, a prime divisor of "
                        + "the rank of p is smaller than p when p exceeds five; the ranks "
                        + "at two, three and five contribute only primes at most five. "
                        + "The expanding sets therefore stay inside the finite universe "
                        + "of primes at most B. Equal cardinalities on successive steps "
                        + "give a fixed point, and induction gives its leastness."))),
                DescribeRole.Theorem)),
        []));
}
