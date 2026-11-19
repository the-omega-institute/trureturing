using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class FiniteLinePrefixCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform counting of finite line prefixes", H("Uniform counting of finite line prefixes"), Blocks(
            Describe.Lean(DescribeId.Create("prefix"), DeclarationHandle.Create(Prefix + "Prefix"),
                H("Actual tuples with distinct column labels"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Let V be finite, let L_j be prescribed finite subsets of V, and let c map vertices to a label type. A prefix of length k is a function f from Fin k to V such that f(i) belongs to L_i and the labels c(f(i)) are pairwise distinct. These are actual finite tuples, with no recursively defined substitute for their cardinality."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bound"), DeclarationHandle.Create(Prefix + "card_prefix_lower_bound"),
                H("A uniform lower bound at every prefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For all natural m and K, suppose c is injective on every L_j and the cardinality of L_j is at least m+j for every j<K. Then the number of prefixes of length K is at least m^K. For a fixed prefix of length j, its used labels forbid at most j vertices of L_j, leaving at least m choices. Appending a legal vertex is injective on the dependent pair consisting of that prefix and its next choice. Summing these fiber cardinalities and inducting on j gives the bound. The lower bound holds for every prefix on the same family; it does not multiply separately attainable optima."))), DescribeRole.Theorem)), []));
}
