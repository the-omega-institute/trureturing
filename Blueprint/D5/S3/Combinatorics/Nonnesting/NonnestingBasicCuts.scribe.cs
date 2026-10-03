using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicCutsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicCuts.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order separation splits a doubled word.",
        H("Separated Value Cuts"),
        Blocks(
            Node("nonnesting-nonnestingbasiccuts-filter-partition-of-separated", "Filtering a separated word", "filter_partition_of_separated",
                "If every entry at most k precedes every larger entry, the word is the concatenation of its two value filters.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasiccuts-valuecut-of-separated-indices", "Separation gives a value cut", "valueCut_of_separated_indices",
                "In a doubled permutation, separation of entries at most k from larger entries establishes a value cut at k.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
