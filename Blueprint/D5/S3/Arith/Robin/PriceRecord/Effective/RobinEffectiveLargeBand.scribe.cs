using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord.Effective;

internal sealed class RobinEffectiveLargeBandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveLargeBand.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual weighted zero bound and explicit arithmetic prove the effective Robin inequality above 5040.",
        H("Effective Robin inequality above 5040"),
        Blocks(
            Paragraph(Text("The proof applies the full prime-power ledger to the same integer and real cutoff supplied by the attained failure minimum. The tangent rows cover log height through 101. The five exact prime rosters cover real cutoffs from 100 through 10000. For z ≥ 10000, Abel summation and the weighted zero bound give the prime-square band a normalized surplus of at least 17692481023/192060000000.")),
            Describe.Lean(DescribeId.Create("large-band"), DeclarationHandle.Create(Prefix + "normalized_prime_band_large"),
                H("Strict reserve for large cutoffs"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every actual zero occurrence has real part 1/2, then for every real z ≥ 10000 the normalized prime-band surplus strictly exceeds the combined error and curvature budget (1 + 1/log z)/20 + 2/√z + (1 + 1/log z)/(8z√z)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-margin"), DeclarationHandle.Create(Prefix + "effective_robin_margin"),
                H("Positive Robin log margin"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every actual zero occurrence has real part 1/2, the Robin log margin of each natural number n > 5040 is strictly positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("line-inequality"), DeclarationHandle.Create(Prefix + "effective_robin_of_line"),
                H("Divisor-sum inequality on the zero line"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every actual zero occurrence has real part 1/2, then for every natural number n > 5040 the sum of its positive divisors is strictly less than exp(γ) · n · log(log(n)), where γ is Euler’s constant."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-inequality"), DeclarationHandle.Create(Prefix + "effective_robin_of_rh"),
                H("Divisor-sum inequality under the Riemann hypothesis"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Riemann hypothesis puts every actual zero occurrence on the critical line. It follows that for every natural number n > 5040 the sum of its positive divisors is strictly less than exp(γ) · n · log(log(n))."))), DescribeRole.Theorem)
        )));
}
