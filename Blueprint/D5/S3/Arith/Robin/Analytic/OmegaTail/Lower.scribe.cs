using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class LowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective selection of prime subsets.", H("Injective selection of prime subsets"), Blocks(
            Describe.Lean(DescribeId.Create("multibox-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.multibox_bound"),
                H("Prime bin counting"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite index type, pairwise disjoint finite prime bins P(j), prescribed natural cardinalities k(j), positive real bounds B(j), real lambda and positive cutoff x, suppose every prime in P(j) is at most B(j), the sum of k(j) exceeds the distinct-prime threshold, and the sum of k(j)*log(B(j)) is at most log(x). Then the product of choose(card(P(j)),k(j)) is at most tailCount(lambda,x). There is no capacity assumption: an impossible selection has binomial coefficient zero. Unique prime factorization makes products of different prime subsets distinct. Disjointness recovers each component from its union. Each selected product is positive, has exactly the sum of k(j) distinct prime factors, and fits below x by its logarithmic cost."))), DescribeRole.Theorem))));
}
