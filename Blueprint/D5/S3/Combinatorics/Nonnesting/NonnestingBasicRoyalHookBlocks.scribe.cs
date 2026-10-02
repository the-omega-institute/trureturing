using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicRoyalHookBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalHookBlocks.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutations avoiding 123 and 132 decompose into hook-shaped blocks.",
        H("Hook-Block Decomposition"),
        Blocks(
            Node("nonnesting-nonnestingbasicroyalhookblocks-hook-blocks", "Hook-block permutation", "hookBlocks",
                "For a block of size k with largest remaining value n, list n minus one down through n minus k plus one, followed by n. Concatenate this block with the blocks constructed from the remaining sizes and the remaining largest value n minus k.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicroyalhookblocks-avoids-has-hook-blocks", "Existence of hook blocks", "avoids_has_hook_blocks",
                "Every permutation of one through n avoiding 123 and 132 is a concatenation of hook-shaped blocks whose positive sizes sum to n.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
