using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class PrimeGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/PrimeGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The gap after the n-th prime is positive, and the factorial construction makes it "
            + "exceed any prescribed bound.",
        H("Gaps between consecutive primes"),
        Blocks(
            Paragraph(Text(
                "Indexing the primes in increasing order gives a gap function on the naturals. "
                    + "Positivity records that consecutive primes are distinct; unboundedness is "
                    + "the classical consequence of the fact that a factorial is divisible by "
                    + "every small number, which produces an interval containing no prime at all.")),
            Describe.Lean(
                DescribeId.Create("prime-gap-definition"),
                DeclarationHandle.Create(Prefix + "primeGap"),
                H("The gap function"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural number n, primeGap n is the difference between the prime of "
                        + "index n plus one and the prime of index n, where the primes are "
                        + "enumerated in increasing order starting from two at index zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-gap-positive"),
                DeclarationHandle.Create(Prefix + "primeGap_pos"),
                H("Positivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every gap is positive. The primes form an infinite set of naturals, so their "
                        + "increasing enumeration is strictly monotone, and the difference of a "
                        + "term from its successor is a difference of a strictly smaller natural "
                        + "from a larger one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-gap-unbounded"),
                DeclarationHandle.Create(Prefix + "exists_primeGap_ge"),
                H("Gaps exceed every bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural number N there is an index whose gap is at least N. Put m "
                        + "equal to N plus two. Each of the m minus one consecutive integers from "
                        + "the factorial of m plus two up to the factorial of m plus m is "
                        + "composite, because the offset divides the factorial and divides itself, "
                        + "while the sum exceeds the offset. That interval therefore contains no "
                        + "prime. Taking the first index whose prime exceeds the factorial of m "
                        + "plus one, the prime at the preceding index lies below that threshold "
                        + "and the prime at that index lies above the whole interval, so the gap "
                        + "at the preceding index is at least m minus one, which is at least N. "
                        + "The classical factorial construction is carried out here rather than "
                        + "taken from an existing statement of the same conclusion."))),
                DescribeRole.Theorem)),
        []));
}
