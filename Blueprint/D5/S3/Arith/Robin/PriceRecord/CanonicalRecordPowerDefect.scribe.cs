using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class CanonicalRecordPowerDefectDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/CanonicalRecordPowerDefect";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict record has a power-scale defect at every real reference at least exp(4). "
        + "At integer references its complete first-layer loss has an exact prime-or-composite formula.",
        H("Canonical record power defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-record-power-defect"),
                DeclarationHandle.Create(Gid + ".canonical_record_power_defect"),
                H("Power defect at a real reference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be real with exp(4) ≤ X. Set q = referencePrice(X) = 1/(X log X), "
                        + "μ = firstLayerPrice(X + 1) = log(1 + 1/(X + 1))/log(X + 1), and "
                        + "m = strictInteger(μ). Then μ > 0 and m ≥ 2. The integer m optimizes the "
                        + "original objective at μ and strictly beats every positive integer smaller "
                        + "than m at that price (FullRecord m μ). For every natural p, membership "
                        + "in m.primeFactors is equivalent to p being prime and p < X + 1 in ℝ. "
                        + "The prices satisfy (1 − 3/X)q ≤ μ < q.")),
                    Paragraph(Text(
                        "Let M be the sum of log p over the symmetric difference of the higher-layer "
                        + "inventories of m and strictInteger(q). The inventory of an integer n "
                        + "consists of the pairs (p, j) with p prime and 2 ≤ j ≤ the exponent of p in n. "
                        + "Write D = actualDefect(X, m), the unrestricted optimum at q minus the "
                        + "objective of m at q, and R = D − completeFirstLayerLoss(X, m). Then "
                        + "M ≤ 800(log X)² and 0 ≤ R ≤ 2400 log X/X². For every p in lossPrimes(X, m), "
                        + "the union of the prime supports of strictInteger(q) and m, a nonzero "
                        + "layerLoss(X, m, p, 1) implies X − 1/2 < p < X + 1 in ℝ. Summing these "
                        + "first-layer losses over the full union gives "
                        + "0 ≤ completeFirstLayerLoss(X, m) ≤ 5/X², "
                        + "and 0 ≤ D ≤ (2400 log X + 5)/X².")),
                    Paragraph(Text(
                        "The strict layer rule includes exactly the layers with marginal above the "
                        + "price. The strict optimizer divides every optimizer at the same price, "
                        + "which gives full recordhood. On the first layer, monotonicity gives the "
                        + "support cutoff. If a prime equals X + 1, its first-layer marginal equals μ, "
                        + "so the strict rule omits that layer. Using X > 16 and log X ≥ 4, "
                        + "the bounds log(X + 1) ≤ log X + 1/X and log(1 + 1/(X + 1)) ≥ 1/(X + 2) "
                        + "give the lower price bracket. The strict first-layer price decrease "
                        + "and log(1 + 1/X) < 1/X give the upper bracket.")),
                    Paragraph(Text(
                        "The inventories are nested as the price decreases. With s = 3/X, the "
                        + "mismatch is bounded by the higher logarithmic mass lost when the price "
                        + "increases from (1 − s)q to (1 + s)q. The mass response bounds this by "
                        + "400(s√X log X + (log X)²) ≤ 800(log X)². The complete higher-loss identity "
                        + "gives zero loss on the common inventory. Each extra coordinate of m "
                        + "has marginal in (μ, q] and contributes (q − marginal) log p, "
                        + "which is zero at a tie with q. Summing gives 0 ≤ R ≤ (q − μ)M, "
                        + "and the bracket yields the stated bound on R.")),
                    Paragraph(Text(
                        "An unoccupied first coordinate has nonpositive margin at q and zero loss. "
                        + "The first-layer price equals q at a real cutoff ρ with X − 1/2 < ρ < X. "
                        + "An occupied coordinate at or below ρ also has zero loss. The remaining "
                        + "nonzero terms lie in (X − 1/2, X + 1), which contains at most two natural "
                        + "integers. Each term is q log p − log(1 + 1/p), at most "
                        + "2/(X(X + 2)) + 1/(X² log X) ≤ 9/(4X²). The full sum therefore lies "
                        + "between zero and 5/X². Adding it to R gives the bounds on D."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-integer-first-loss"),
                DeclarationHandle.Create(Gid + ".canonical_integer_first_loss"),
                H("Exact first-layer loss at an integer reference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let N be a natural number whose real value is at least exp(4). Set "
                        + "μ = firstLayerPrice(N + 1) and m = strictInteger(μ), using the real "
                        + "value of N in the price and loss formulas. The complete first-layer "
                        + "loss completeFirstLayerLoss(N, m) is 1/N − log(1 + 1/N) when N is prime "
                        + "and zero when N is composite.")),
                    Paragraph(Text(
                        "The only natural number in (N − 1/2, N + 1) is N, so every other term "
                        + "of the complete sum vanishes. If N is prime, its first layer is occupied "
                        + "because N < N + 1. Its cost referencePrice(N) × log N equals 1/N, which "
                        + "strictly exceeds the gain log(1 + 1/N). The loss is their difference. If N is "
                        + "composite, every index in the union of prime supports differs from N."))),
                DescribeRole.Theorem))));
}
