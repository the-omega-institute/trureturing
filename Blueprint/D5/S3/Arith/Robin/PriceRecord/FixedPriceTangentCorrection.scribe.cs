using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedPriceTangentCorrectionDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentCorrection";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The tangent curvature correction for the literal integer prime prefix.",
        H("Tangent curvature correction on prime prefixes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-price-tangent-correction-tendsto"),
                DeclarationHandle.Create(Gid + ".fixed_price_tangent_correction_tendsto"),
                H("Unit limit for the scaled gap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each natural P, use exactly the primes p ≤ P, with each integer "
                        + "exponent at least one. Let H be the sum of log p over this prefix. "
                        + "For sufficiently large P, we have 1 < H. On prefixes with 1 < H, "
                        + "the fixed-price linear cost at 1/(H log H) attains its minimum V "
                        + "and the nonlinear integer cost on the same support attains its infimum I. "
                        + "As P tends to infinity, H log H · (V − I) tends to one.")),
                    Paragraph(Text(
                        "The nonlinear sublevel through the all-ones vector bounds each "
                        + "supported exponent, so a finite product contains an exact minimizer. "
                        + "Concavity makes that vector minimize the linear cost at its own "
                        + "clock price. Eventually the relative price deficit lies between "
                        + "zero and 4(log H)I. The fixed-price minimizer clock theorem applies "
                        + "at both prices and gives a clock increment asymptotic to √(2H) "
                        + "for each vector.")),
                    Paragraph(Text(
                        "The tangent remainder at the prefix-price minimizer bounds V − I "
                        + "from below. The tangent remainder at the nonlinear minimizer bounds "
                        + "it from above. The quadratic bounds for the log-log tangent gap "
                        + "give limit one for both remainders after multiplication by H log H."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tangent-remainder-quadratic"),
                DeclarationHandle.Create(Gid + ".tangent_remainder_quadratic"),
                H("Curvature bounds at a nonnegative clock increment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For H > 1 and u ≥ 0, the tangent remainder from H to H + u lies "
                    + "between u²/2 times the activation density at H + u and u²/2 times "
                    + "the density at H. The global log-log tangent bounds give the two "
                    + "endpoints since H ≤ H + u."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-minimizers-tangent-bounds"),
                DeclarationHandle.Create(Gid + ".prefix_minimizers_tangent_bounds"),
                H("Bounds from the two prefix minimizers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On sufficiently large prime prefixes, one can choose a fixed-price "
                    + "minimizer and a nonlinear minimizer that also minimizes the linear cost "
                    + "at its own clock price. Their increments are nonnegative. The relative "
                    + "own-price error is bounded by a constant divided by √H. The scaled "
                    + "remainders at the two increments bound the scaled gap from below and above, "
                    + "respectively."))),
                DescribeRole.Theorem))));
}
