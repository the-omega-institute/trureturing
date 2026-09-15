using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class DistinctPrimePrefixWordCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct Initial Labels in Occupation Words.",
        H("Distinct Initial Labels in Occupation Words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("distinctprimeprefixwordcount-factorial"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/DistinctPrimePrefixWordCount.distinct_prefix_count_factorial"),
                H("Counting words with a distinct prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a be a finite multiset of labels, let r be its cardinality, and let j lie "
                    + "between zero and r. Count the words with occupation a whose first j labels "
                    + "are pairwise distinct. Multiplying this count by the product of the "
                    + "multiplicity factorials gives j! times (r-j)! times the elementary symmetric "
                    + "coefficient of degree j in the multiplicities. The formula includes zero "
                    + "multiplicities and the empty word. Partitioning each word at position j "
                    + "and then by its set of initial labels gives the count."))),
                DescribeRole.Theorem))));
}
