using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class ConvexSequenceGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/ConvexSequenceGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strictly increasing integer sequence with nondecreasing gaps outgrows every multiple "
            + "of n squared exactly when its gaps outgrow every multiple of n.",
        H("Growth of convex integer sequences"),
        Blocks(
            Paragraph(Text(
                "Nondecreasing consecutive gaps make the growth of a sequence and the growth of "
                    + "its gaps two readings of one fact: the sequence is a partial sum of the "
                    + "gaps, and monotonicity turns that sum into a two-sided estimate by a single "
                    + "gap. The equivalence below records the exchange rate, which is one power "
                    + "of the index.")),
            Describe.Lean(
                DescribeId.Create("consecutive-gap"),
                DeclarationHandle.Create(Prefix + "gap"),
                H("The gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a sequence of naturals, gap q n is the difference of the term at n plus "
                        + "one from the term at n, taken in the naturals. Under the strict "
                        + "monotonicity assumed below the subtraction is never truncated."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("convex-sequence"),
                DeclarationHandle.Create(Prefix + "ConvexSequence"),
                H("Convex sequences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A sequence of naturals is convex when it is strictly monotone and each gap "
                        + "is at most its successor. No further arithmetic property is assumed; in "
                        + "particular the terms are not required to be prime."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quotient-gap-equivalence"),
                DeclarationHandle.Create(Prefix + "quotient_tendsto_atTop_iff_gap_tendsto_atTop"),
                H("The equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a convex sequence q, the real quotient of q n by n squared tends to "
                        + "infinity if and only if the quotient of gap q n by n does. "
                        + "From the gaps to the sequence: monotone gaps give the tail estimate "
                        + "that the term at m plus t is at least the term at m plus t times the "
                        + "gap at m; taking m to be half of n yields a fixed positive multiple of "
                        + "the gap at m divided by m as a lower bound for the quotient at n, and "
                        + "the half-index map itself tends to infinity. "
                        + "From the sequence to the gaps: the same tail estimate read upwards "
                        + "bounds the term at n by the initial term plus n times the gap at n, so "
                        + "the quotient at n is at most the initial term divided by n squared "
                        + "plus the gap quotient; the first summand is eventually at most one, so "
                        + "divergence of the quotient forces divergence of the gap quotient."))),
                DescribeRole.Theorem)),
        []));
}
