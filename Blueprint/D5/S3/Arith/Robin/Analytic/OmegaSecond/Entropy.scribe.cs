using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class EntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite binomial entropy lower bound with an explicit logarithmic loss.",
        H("Finite binomial entropy lower bound"), Blocks(
            Describe.Lean(DescribeId.Create("log-choose-ge-binentropy"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.log_choose_ge_binEntropy"),
                H("Maximum-term entropy bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural a at most m, log choose(m,a) is at least m*binEntropy(a/m)-log(m+1), including the endpoint cases. At p=a/m the binomial probabilities increase up to a and decrease after a, as their adjacent-term recurrence shows. Their sum is one, so the a-th term is at least 1/(m+1). Taking logarithms yields the bound. This is the finite maximum-term argument, with no Stirling estimate or asymptotic hypothesis. In the second-threshold construction it estimates the number of choices in each prime box; feasibility is proved separately by the exchange budget. The equal-number exchange method around a primorial and its partition-constant mechanism have precedent in Erdős–Nicolas 1981, section 1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("entropy-lower"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropyLower"),
                H("Finite entropy estimate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("entropyLower(m,a) is m*binEntropy(a/m)-log(m+1), the lower estimate supplied by the maximum-term theorem."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("entropy-lower-scaled"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.entropy_lower_scaled"),
                H("Entropy on a growing common scale"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On any filter, suppose W tends to infinity, n/W tends to d>0, and k/W tends to d*q. Then entropyLower(n,k)/W tends to d*binEntropy(q). Continuity of binary entropy controls the first term; log(n+1)/(n+1) tends to zero and (n+1)/W tends to d, so the explicit finite loss disappears."))), DescribeRole.Theorem),
Describe.Lean(
                DescribeId.Create("correction-majorant"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.KernelLimit.correctionMajorant"),
                H("Correction majorant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The majorant is pi^2/(6*(1-pi^2/(6*s^2))). Its denominator is positive for s at least pi."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kernel-correction-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.KernelLimit.kernel_correction_upper"),
                H("Cubic sine bound for the correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real s at least pi, s*(pi/sin(pi/s)-s) is nonnegative and at most the correction majorant. The cubic lower bound for sine preserves the coefficient one sixth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("majorant-limit"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.KernelLimit.correction_majorant_limit"),
                H("Explicit limiting majorant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The correction majorant tends to pi^2/6 as s tends to positive infinity. This coefficient controls the localized prime-weight upper estimate. A matching lower bound for the second distinct-prime counting threshold is not established here."))),
                DescribeRole.Theorem),
Describe.Lean(
                DescribeId.Create("finite-power-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Tail.finite_power_tail"),
                H("Finite inverse-power tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real s>1, every positive natural cutoff N, and every finite set S of natural numbers strictly larger than N, the sum of n^(-s) over S is at most N^(1-s)/(s-1). The bound compares the finite sum with the integral over all real t>N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("small-weight-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Tail.small_weight_tail"),
                H("Small-endpoint geometric tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For P>=2 and s>=0, summing log(1+exp(-s*abs(log(n/P)))) over any finite set of positive natural numbers n<=P/2 gives at most P*(1/2)^s. This bound also applies to any selected primes in that range."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("large-weight-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Tail.large_weight_tail"),
                H("Large-endpoint geometric tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For P>=2 and s>=2, the same localized weight summed over any finite set of natural numbers strictly greater than 2P is at most 2P*(2/3)^s. The real-to-natural cutoff is retained explicitly before the inverse-power tail estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geometric-sqrt-decay"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.Tail.geometric_sqrt_decay"),
                H("Decay at the square-root logarithmic saddle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every fixed c>0 and 0<q<1, t*sqrt(t)*q^(c*sqrt(t)) tends to zero as t tends to positive infinity. Thus each geometric tail vanishes on the normalized second-threshold scale at its explicit saddle. A matching lower counting bound is not established here."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("floor-scaled"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.floor_scaled"),
                H("Rounded occupancy on a common scale"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If W tends to infinity and M/W tends to d>0, then floor(q*M)/W tends to q*d for every fixed nonnegative q. The pinned floor-ratio limit is composed with M tending to infinity and multiplied by M/W."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("min-scaled"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy.min_scaled"),
                H("Common capacity on a common scale"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If two natural capacities divided by a positive growing scale both tend to d, then their minimum divided by the scale also tends to d. This supplies the equal capacity used for the two sides of each prime-box exchange."))), DescribeRole.Theorem))));
}
