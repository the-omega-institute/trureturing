using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.GronwallAbundant;

internal sealed class CodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-deletion constraints, missing-prime mass and finite-code entropy for proper GA1 integers.",
        H("Coding"),
        Blocks(
            Describe.Lean(DescribeId.Create("small-subsets-card"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Coding.small_subsets_card"), H("Subsets with bounded cardinality are partitioned by their actual sizes."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subsets with bounded cardinality are partitioned by their actual sizes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("binomial-partial-sum-weighted"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Coding.binomial_partial_sum_weighted"), H("A truncated binomial sum is controlled by its generating polynomial."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A truncated binomial sum is controlled by its generating polynomial."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("binomial-partial-sum-entropy"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Coding.binomial_partial_sum_entropy"), H("The missing-set choices satisfy the elementary binomial entropy bound."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The missing-set choices satisfy the elementary binomial entropy bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primeend"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Coding.primeEnd"), H("The last prime in the support, with value zero for the empty support."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The last prime in the support, with value zero for the empty support."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upperholes"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Coding.upperHoles"), H("Missing primes above the small-prime cutoff in the support prefix."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Missing primes above the small-prime cutoff in the support prefix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primecode"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Coding.primeCode"), H("The prime prefix endpoint, all small exponents, and the omitted large primes."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The prime prefix endpoint, all small exponents, and the omitted large primes."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primecode-injective-on"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Coding.primeCode_injective_on"), H("An integer with only squarefree large prime factors is recovered from its code."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An integer with only squarefree large prime factors is recovered from its code."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-code-card-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GronwallAbundant/Coding.prime_code_card_bound"), H("A finite collection of integers with bounded codes satisfies the coding bound."),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite collection of integers with bounded codes satisfies the coding bound."))), DescribeRole.Theorem))));
}
