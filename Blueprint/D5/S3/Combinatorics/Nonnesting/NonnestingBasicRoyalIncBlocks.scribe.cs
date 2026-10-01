using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicRoyalIncBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalIncBlocks.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutations avoiding 132 and 213 decompose into increasing blocks with decreasing value ranges.",
        H("Increasing-Block Decomposition"),
        Blocks(
            Node("nonnesting-nonnestingbasicroyalincblocks-inc-blocks", "Increasing-block permutation", "incBlocks",
                "For a block of size k with largest remaining value n, list n minus k plus one through n in increasing order. Concatenate this block with the blocks constructed from the remaining sizes and the remaining largest value n minus k.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicroyalincblocks-avoids-has-inc-blocks", "Existence of increasing blocks", "avoids_has_inc_blocks",
                "Every permutation of one through n avoiding 132 and 213 is a skew sum of increasing blocks whose positive sizes sum to n.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
