using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class LowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective selection of prime subsets.", H("Injective selection of prime subsets"), Blocks(
            Describe.Lean(DescribeId.Create("prime-product-injective"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.prime_product_injective"),
                H("Prime products recover their support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite sets of primes with equal products are equal. The proof directly applies Mathlib's primeFactors_prod to both products."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("omega-prime-product"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.omega_prime_product"),
                H("Distinct-prime count of a prime product"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The number of distinct prime factors of a finite prime-set product is exactly the cardinality of the set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-family-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.prime_family_bound"),
                H("Prime-set families enter the literal tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite family of prime subsets whose cardinalities exceed the threshold and whose logarithmic costs do not exceed log(x) injects into tailCount(lambda,x), for x positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bin-union-inter"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.bin_union_inter"),
                H("Recover a component from a disjoint union"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intersecting the union of selected subsets with one of their pairwise disjoint ambient bins recovers exactly that bin's selected subset."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("multibox-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.multibox_bound"),
                H("Prime bin counting"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite index type, pairwise disjoint finite prime bins P(j), prescribed natural cardinalities k(j), positive real bounds B(j), real lambda and positive cutoff x, suppose every prime in P(j) is at most B(j), the sum of k(j) exceeds the distinct-prime threshold, and the sum of k(j)*log(B(j)) is at most log(x). Then the product of choose(card(P(j)),k(j)) is at most tailCount(lambda,x). There is no capacity assumption: an impossible selection has binomial coefficient zero. Unique prime factorization makes products of different prime subsets distinct. Disjointness recovers each component from its union. Each selected product is positive, has exactly the sum of k(j) distinct prime factors, and fits below x by its logarithmic cost."))), DescribeRole.Theorem))));
}
