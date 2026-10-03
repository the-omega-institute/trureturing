using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class OriginalOddDepthSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/OriginalOddDepthSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under the prime-index odd-factor input, odd original depth bounds Fibonacci index and squarefree-kernel support.",
        H("Original odd-depth support"),
        Blocks(
            Paragraph(Text(
                "Fix a positive index n, a finite set S of primes greater than five, "
                    + "and its Fibonacci rank closure H(S). Assume that each prime ell "
                    + "greater than five dividing n has a prime factor of F_ell with "
                    + "odd valuation. The prime-to-index valuation equality applies "
                    + "to factors p that do not divide n.")),
            Describe.Lean(
                DescribeId.Create("prime-index-odd-factor"),
                DeclarationHandle.Create(Prefix + "PrimeIndexOddFactor"),
                H("Prime-index input"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each prime ell greater than five dividing n, some prime factor "
                        + "of the original F_ell has odd valuation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("odd-depth-kernel"),
                DeclarationHandle.Create(Prefix + "oddDepthKernel"),
                H("Odd-depth squarefree kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The product of the distinct prime factors occurring to odd "
                        + "multiplicity in the original Fibonacci value F_n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-support-descent"),
                DeclarationHandle.Create(Prefix + "original_odd_depth_support"),
                H("Index and kernel support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose every prime factor p greater than five of F_n that does "
                        + "not divide n and has odd valuation at its first Fibonacci "
                        + "zero belongs to S. Then every prime factor of n belongs to "
                        + "H(S). The proof chooses the largest index prime outside H(S). "
                        + "A prime factor of its Fibonacci block is larger than that "
                        + "index prime and has that exact first-zero rank. If it divided "
                        + "n, maximality and closure would give a contradiction. It is "
                        + "therefore an external odd-depth factor, giving the same "
                        + "contradiction through S. Small primes belong to H(S) by "
                        + "definition, and factors dividing n belong to it by index "
                        + "support. The remaining odd-exponent factors belong to H(S) "
                        + "by the original-depth condition and the prime-to-index "
                        + "valuation formula. Thus the squarefree kernel divides the product "
                        + "of the primes in H(S)."))),
                DescribeRole.Theorem)),
        []));
}
