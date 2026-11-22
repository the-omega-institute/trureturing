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
                DescribeRole.Theorem))));
}
