using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class ElementaryCyclotomicWeightedCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime-power weighted carry identity and its explicit linear sampled correction.",
        H("Weighted cyclotomic correction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-readout"),
                DeclarationHandle.Create(Prefix + "primePowerReadout"),
                H("Prime-power readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each prime power p^t at most X with t positive, multiply the coefficient at "
                        + "p^t by its weight and by log p, then add the contributions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-psi"),
                DeclarationHandle.Create(Prefix + "weightedPsi"),
                H("Weighted Chebyshev sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Set every coefficient in the prime-power readout to one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-von-mangoldt"),
                DeclarationHandle.Create(Prefix + "weightedPsi_eq_sum_vonMangoldt"),
                H("Weighted von Mangoldt sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real-valued weight on the natural numbers and every natural cutoff x, "
                        + "the readout equals the sum of w(n) times the von Mangoldt function at n for "
                        + "1 ≤ n ≤ x.")),
                    Paragraph(Text(
                        "Each prime power has a unique prime base and positive exponent. This bijection "
                        + "identifies the summands, and the von Mangoldt function vanishes off prime powers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-carries"),
                DeclarationHandle.Create(Prefix + "weightedB"),
                H("Weighted carries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At cutoff 4N+1, the coefficient of a conductor is the sum of the row carries "
                        + "and the sum of the carries restricted by the index-dependent gcd cutoffs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-factorial-correction"),
                DeclarationHandle.Create(Prefix + "weightedK"),
                H("Weighted factorial correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At cutoff 4N+1, assign coefficient N to conductor two, the floor of N/r to each "
                        + "odd conductor r, and zero to higher powers of two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-indicator"),
                DeclarationHandle.Create(Prefix + "weightedIndicator"),
                H("Weighted residue indicator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Read the residue indicator at each prime power through cutoff 4N+1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-weighted-carry-identity"),
                DeclarationHandle.Create(Prefix + "weightedB_add_weightedK_add_weightedIndicator"),
                H("Exact weighted carry identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary real weights and every natural N, the weighted carries, factorial "
                        + "correction and residue indicator add up to the sum of weighted Chebyshev values "
                        + "at 4i+1 for 0 ≤ i ≤ N.")),
                    Paragraph(Text(
                        "The prime-power deficit equals the factorial coefficient plus the residue "
                        + "indicator. Padding the sampled sums to the common cutoff 4N+1 gives the same "
                        + "coefficient at each prime power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("corrected-weighted-sample-error"),
                DeclarationHandle.Create(Prefix + "corrected_weighted_sample_error"),
                H("Explicit weighted sample error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural N and every nonnegative bound W with 0 ≤ w(r) ≤ W for all r, "
                        + "the absolute difference between the weighted carries plus factorial correction "
                        + "and the sum of weighted Chebyshev values at 4i for 0 ≤ i ≤ N is at most "
                        + "W times (4N+1) times (log 4 + 4).")),
                    Paragraph(Text(
                        "The residue indicator contributes between zero and W times (4N+1) log 4. The "
                        + "change from 4i to 4i+1 also contributes a nonnegative amount. Each prime power "
                        + "can occur at only one of these boundaries, so the Chebyshev bound controls "
                        + "their total contribution."))),
                DescribeRole.Theorem))));
}
