using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class QuantitativeMovingPriceMinimizerClockDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/QuantitativeMovingPriceMinimizerClock";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quantitative clock limit of supported integer Robin minimizers.",
        H("All fixed logarithmic orders for the clock at a moving price"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-price-minimizer-clock-log-power-tendsto"),
                DeclarationHandle.Create(Gid + ".moving_price_minimizer_clock_log_power_tendsto"),
                H("Quantitative convergence to the second-layer prefix cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H = θ(P). For each fixed natural n and real C, suppose the "
                        + "moving price λ satisfies |λ/prefixPrice(P) − 1| ≤ C/√H "
                        + "eventually. Choose any eventual supported integer minimizers "
                        + "of the linear cost on the primes p ≤ P. The difference between "
                        + "their clock increment and the second-layer cutoff at prefixPrice(P), "
                        + "multiplied by (log H) raised to n and divided by √H, tends to zero.")),
                    Paragraph(Text(
                        "The price bound keeps the two actual cutoffs a bounded distance apart. "
                        + "At the moving cutoff t, the second layer includes primes strictly "
                        + "below t and excludes primes strictly above it. Its log sum is "
                        + "between θ(t − 1) and θ(t), including when a prime ties at t. "
                        + "The quantitative prime estimate applies at both endpoints. "
                        + "The finite bound for every layer of index at least three "
                        + "also vanishes after the same logarithmic weighting."))),
                DescribeRole.Theorem))));
}
