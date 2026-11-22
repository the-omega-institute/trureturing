using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedLayerAggregateDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/FixedLayerAggregate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-layer approximation and residual limits for the supported integer Robin infimum.",
        H("All fixed layers of the integer Robin infimum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-integer-infimum-all-fixed-layers"),
                DeclarationHandle.Create(Gid + ".actual_integer_infimum_all_fixed_layers"),
                H("Approximation through any fixed layer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a natural m ≥ 2. For each natural P put H = θ(P) and ℓ = log H. "
                        + "Let I(P) be the infimum of the original nonlinear Robin cost "
                        + "over all integer exponent vectors with exponent at least one at "
                        + "each prime p ≤ P. The cost uses the prime prefix as its support. "
                        + "For each j, let A_j(P) be the sum of "
                        + "min(prefixPrice(P) log p, 1/p^j) over those primes. "
                        + "The prefix price is 1/(Hℓ). As P tends to infinity, "
                        + "the difference between I(P) and the sum of A_j(P) for 2 ≤ j ≤ m, "
                        + "multiplied by H^((m−1)/m) ℓ, tends to zero.")),
                    Paragraph(Text(
                        "At the tangent price, the finite omitted-layer bound uses a "
                        + "logarithmic exponent cap for primes up to H^(1/(m+1)) and the "
                        + "cap m above that cutoff. Chebyshev's bound and the finite inverse-power "
                        + "tail bound give an omitted contribution of order H^(−m/(m+1)). "
                        + "For each retained layer j, the clipped reciprocal power and the clipped Euler "
                        + "marginal agree up to H^(1/j). The sum of their differences above it is at most 2/H. "
                        + "A quadratic bound for the log-log tangent remainder on the "
                        + "H^(−1/2) sublevel bounds the gap between the nonlinear infimum and "
                        + "the tangent minimum by 16ℓ/H for all sufficiently large P. "
                        + "Both contributions to the resulting error vanish after scaling."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-integer-infimum-fixed-layer-residual"),
                DeclarationHandle.Create(Gid + ".actual_integer_infimum_fixed_layer_residual"),
                H("Residual after subtracting the preceding layers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every fixed natural m ≥ 2, take the difference between I(P) "
                        + "and the finite sum of the same A_j(P) for 2 ≤ j ≤ m−1. "
                        + "After multiplication by H^((m−1)/m) ℓ, this tends to "
                        + "(m/(m−1)) m^(1/m) as P tends to infinity. "
                        + "For m = 2 the sum is empty.")),
                    Paragraph(Text(
                        "Splitting off the last summand of the finite layer sum writes "
                        + "the scaled residual as the scaled approximation error plus "
                        + "the scaled A_m(P). The approximation error tends to zero and "
                        + "the fixed-layer prime-tail limit supplies the constant."))),
                DescribeRole.Theorem))));
}
