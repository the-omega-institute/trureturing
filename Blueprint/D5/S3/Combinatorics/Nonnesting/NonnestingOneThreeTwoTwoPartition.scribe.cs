using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoPartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoPartition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prefix before a pivot separates larger letters from smaller letters.",
        H("Prefix Partition for 1322 Avoidance"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwopartition-prefix-partition", "Partition before the first pivot", "prefix_partition",
                "In a word containing exactly two copies of each of its letters and avoiding 1322, the prefix before the first occurrence of any pivot equals its subsequence of letters larger than the pivot followed by its subsequence of letters smaller than the pivot.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
