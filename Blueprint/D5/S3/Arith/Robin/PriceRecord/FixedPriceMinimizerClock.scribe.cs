using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedPriceMinimizerClockDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/FixedPriceMinimizerClock";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The uniform clock limit of supported fixed-price integer Robin minimizers.",
        H("Clock limit for integer Robin minimizers at a moving price"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-price-minimizer-clock-eventually-between"),
                DeclarationHandle.Create(Gid + ".fixed_price_minimizer_clock_eventually_between"),
                H("Uniform clock bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H = θ(P) and let the price λ(P) satisfy λ(P) H log H → 1. "
                        + "Minimize the integer linear cost on the primes p ≤ P, "
                        + "with each exponent at least one. For any l < √2 < r, "
                        + "every minimizer at each sufficiently large P has clock increment "
                        + "strictly between l√H and r√H. The lower cutoff on P is common "
                        + "to all the minimizers at the given prices.")),
                    Paragraph(Text(
                        "Comparing one-coordinate neighbors gives the included and excluded "
                        + "marginal-price inequalities, with ties allowed on either side. "
                        + "The second layer is bounded between the prime log sums at c√H "
                        + "and d√H for any fixed 0 < c < √2 < d. The prime number theorem "
                        + "gives the limits c and d after normalization. For every included "
                        + "layer j ≥ 3, the price inequality bounds p^j by B = 4H log H "
                        + "for large P. These layers contribute at most "
                        + "(log B / log 2) θ(B^(1/3)), which is o(√H)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-price-minimizer-clock-tendsto"),
                DeclarationHandle.Create(Gid + ".fixed_price_minimizer_clock_tendsto"),
                H("Limit for all minimizing selections"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any moving price whose ratio to the prefix price tends to one, "
                        + "let a(P) be any eventual selection of supported minimizers of the "
                        + "literal linear cost. The sum of (a(P)(p) − 1) log p over the "
                        + "support, divided by √H, tends to √2. "
                        + "The uniform two-sided bounds apply to the selected exponent "
                        + "vector at every sufficiently large prefix."))),
                DescribeRole.Theorem))));
}
