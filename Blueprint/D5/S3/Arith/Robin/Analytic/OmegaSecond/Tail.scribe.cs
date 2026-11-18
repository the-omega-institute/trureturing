using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class TailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer majorants for the tails of a moving localized prime weight.",
        H("Geometric tails of the moving weight"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-power-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.finite_power_tail"),
                H("Finite inverse-power tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real s>1, every positive natural cutoff N, and every finite set S of natural numbers strictly larger than N, the sum of n^(-s) over S is at most N^(1-s)/(s-1). The bound compares the finite sum with the integral over all real t>N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("small-weight-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.small_weight_tail"),
                H("Small-endpoint geometric tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For P>=2 and s>=0, summing log(1+exp(-s*abs(log(n/P)))) over any finite set of positive natural numbers n<=P/2 gives at most P*(1/2)^s. This bound also applies to any selected primes in that range."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("large-weight-tail"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.large_weight_tail"),
                H("Large-endpoint geometric tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For P>=2 and s>=2, the same localized weight summed over any finite set of natural numbers strictly greater than 2P is at most 2P*(2/3)^s. The real-to-natural cutoff is retained explicitly before the inverse-power tail estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("geometric-sqrt-decay"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.geometric_sqrt_decay"),
                H("Decay at the square-root logarithmic saddle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every fixed c>0 and 0<q<1, t*sqrt(t)*q^(c*sqrt(t)) tends to zero as t tends to positive infinity. Thus each geometric tail vanishes on the normalized second-threshold scale at its explicit saddle. A matching lower counting bound is not established here."))),
                DescribeRole.Theorem))));
}
