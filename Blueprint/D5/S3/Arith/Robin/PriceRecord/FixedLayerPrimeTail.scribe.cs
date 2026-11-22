using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedLayerPrimeTailDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/FixedLayerPrimeTail";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite prime-power tail limits and the asymptotic of each fixed clipped layer.",
        H("Finite prime-power tails and fixed activation layers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-tail-tendsto"),
                DeclarationHandle.Create(Gid + ".prime_power_tail_tendsto"),
                H("The finite tail with a moving upper endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a natural m ≥ 2. Along any filter on which the real lower "
                        + "endpoint y tends to infinity and the ratio z/y tends to infinity, "
                        + "multiply the sum of 1/p^m over primes y < p ≤ z by "
                        + "y^(m−1) log y. The result tends to 1/(m−1).")),
                    Paragraph(Text(
                        "Finite Abel summation gives two endpoint terms and the prime-count "
                        + "integral. With k = m−1, the negative derivative of "
                        + "1/(u^k log u) compares the integral to an explicit boundary difference. "
                        + "For 1 < y ≤ z, if η bounds 1/log y and the normalized prime-count error throughout "
                        + "the interval, the absolute error in the normalized tail is at most "
                        + "6η + y^k log(y)/(z^k log(z)). The last term is at most "
                        + "y/z. The prime number theorem and the diverging endpoint ratio "
                        + "send these errors to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("activation-layer-tendsto"),
                DeclarationHandle.Create(Gid + ".activation_layer_tendsto"),
                H("The asymptotic constant of a fixed clipped layer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a natural m ≥ 2. For each natural P put H = θ(P) and "
                        + "ℓ = log H, and sum min(prefixPrice(P) log p, 1/p^m) "
                        + "over primes p ≤ P to obtain A_m(P). As P tends to infinity, "
                        + "H^((m−1)/m) ℓ A_m(P) tends to (m/(m−1)) m^(1/m).")),
                    Paragraph(Text(
                        "The cutoff t satisfies t^m log t = Hℓ. Its ratio to "
                        + "H^(1/m) tends to m^(1/m), and P/t tends to infinity. "
                        + "Below the cutoff, the sum uses the price times θ(t). "
                        + "Above it, the sum is the finite prime-power tail on (t,P]. "
                        + "Equality at the cutoff gives the same contribution in either branch. "
                        + "After scaling, the two terms are t/H^(1/m) times the sum of "
                        + "θ(t)/t and the normalized tail. Their inner limits are "
                        + "1 and 1/(m−1), respectively."))),
                DescribeRole.Theorem))));
}
