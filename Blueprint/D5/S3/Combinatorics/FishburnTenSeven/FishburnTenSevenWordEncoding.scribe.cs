using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenWordEncodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWordEncoding.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-letter words allocate entries to decreasing, increasing and trailing decreasing blocks.",
        H("FishburnTenSevenWordEncoding"),
        Blocks(
            Node("fishburntensevenwordencoding-blocks-definition", "Blocks determined by a word", "blocks",
                "For a word indexed from zero through size minus one, assign the value index plus two to the block indicated by its letter. The d and j blocks list their assigned values in decreasing order, and the i block lists its assigned values in increasing order.", DescribeRole.Definition),
            Node("fishburntensevenwordencoding-encodeblocks-definition", "Encoding three blocks", "encodeBlocks",
                "For three lists and an index from zero through size minus one, the encoded letter is d if index plus two belongs to the first list, i if it belongs to the second list but not the first, and j otherwise.", DescribeRole.Definition),
            Node("fishburntensevenwordencoding-reconstruct-definition", "Reconstructing a permutation", "reconstruct",
                "For a word of length size and a total, reconstruction concatenates the decreasing interval with entries from size plus three through total, the d block, one, the i block, size plus two, and the j block. The initial interval is empty when total is at most size plus two.", DescribeRole.Definition),
            Node("fishburntensevenwordencoding-encodepermutation-definition", "Encoding a permutation around one and the peak", "encodePermutation",
                "Cut the list at its first one, taking the whole list as the initial block when one is absent. The middle block is the portion after that one and before the first subsequent entry size plus two, or the whole remaining portion when that entry is absent. For an index from zero through size minus one, encode index plus two as d when it belongs to the initial block, as i when it instead belongs to the middle block, and as j otherwise.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
