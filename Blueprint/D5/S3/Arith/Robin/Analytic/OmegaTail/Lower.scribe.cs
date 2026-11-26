using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class LowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective selection of prime subsets.", H("Injective selection of prime subsets"), Blocks(
            Describe.Lean(DescribeId.Create("prime-product-injective"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.prime_product_injective"),
                H("Recover prime support from its product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two finite prime supports with equal products are equal. Taking prime factors recovers each support."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("omega-prime-product"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.omega_prime_product"),
                H("Count distinct prime factors of a support product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The number of distinct prime factors of a finite prime support's product is the cardinality of that support."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bin-union-inter"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.bin_union_inter"),
                H("Recover a selection from its disjoint bin"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For selections from pairwise disjoint bins, intersect the union of the selections with a bin to recover that bin's selection."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("multibox-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.multibox_bound"),
                H("Prime bin counting"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite index type, pairwise disjoint finite prime bins P(j), prescribed natural cardinalities k(j), positive real bounds B(j), real lambda and positive cutoff x, suppose every prime in P(j) is at most B(j), the sum of k(j) exceeds the distinct-prime threshold, and the sum of k(j)*log(B(j)) is at most log(x). Then the product of choose(card(P(j)),k(j)) is at most tailCount(lambda,x). There is no capacity assumption: an impossible selection has binomial coefficient zero. Unique prime factorization makes products of different prime subsets distinct. Disjointness recovers each component from its union. Each selected product is positive, has exactly the sum of k(j) distinct prime factors, and fits below x by its logarithmic cost."))), DescribeRole.Theorem))));
}
