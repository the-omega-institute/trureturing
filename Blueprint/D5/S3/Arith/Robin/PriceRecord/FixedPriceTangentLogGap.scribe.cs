using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedPriceTangentLogGapDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentLogGap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed-price and nonlinear integer minimizer gap at every fixed logarithmic order.",
        H("Logarithmic precision for the tangent correction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-price-tangent-correction-log-power-tendsto"),
                DeclarationHandle.Create(Gid + ".fixed_price_tangent_correction_log_power_tendsto"),
                H("Centered gap at every fixed logarithmic order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the primes p ≤ P, with H their sum of log p and L = log H. "
                        + "Let V be the fixed-price minimum at the prefix price 1/(H L), I the "
                        + "nonlinear integer infimum on the same support, and U the second-layer "
                        + "cutoff at the prefix price. For each fixed natural n, as P tends to "
                        + "infinity, Lⁿ times the difference between H L (V − I) and "
                        + "(1 + 1/L) U²/(2H) tends to zero.")),
                    Paragraph(Text(
                        "The two prefix minimizers bound H L (V − I) by their scaled tangent "
                        + "remainders. For each nonnegative increment u and log H ≥ 1 with H > 1, "
                        + "the quadratic Q = (1 + 1/L) u²/(2H) exceeds that remainder by at most "
                        + "4(u/H) Q. The moving-price clock estimate compares both increments to U "
                        + "after division by √H at every fixed log order. This controls the "
                        + "difference of the quadratics, and both centered bounds tend to zero."))),
                DescribeRole.Theorem))));
}
