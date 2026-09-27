using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfTwelveSurjectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfTwelveSurject.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every first-pattern avoider with a largest fixed point has the prescribed decorated form.",
        H("Recovering First-Pattern Decorated Data"),
        Blocks(
            Node("block-lengths", "Lengths of inserted blocks", "blockLengths", "The label none stores the initial filler length, while each support-value label stores the length of the block aligned with that value in the skeleton word.", DescribeRole.Definition),
            Node("block-lengths-aligned", "Alignment of block lengths", "blockLengths_aligned", "Reading the labelled lengths in skeleton order gives exactly the list of lengths of the aligned blocks.", DescribeRole.Theorem),
            Node("gaps-of-blocks", "Gap vector recovered from blocks", "gapsOfBlocks", "The initial block and the blocks following support values determine a labelled gap vector with the same total filler length.", DescribeRole.Definition),
            Node("upper-word", "The upper subsequence", "upperWord", "Filtering a word on the full support for entries above m gives a word on the upper support.", DescribeRole.Definition),
            Node("split-lengths-flatten", "Recovering blocks from their lengths", "splitLengths_map_length_flatten", "Splitting the flattening of any list of blocks by that list of block lengths reconstructs the original block list.", DescribeRole.Theorem),
            Node("positive-block", "Upper fixed points require fillers", "positive_block_of_no_upper_fixed", "If an upper skeleton value is fixed there but not in the full word, its following filler block has positive length.", DescribeRole.Theorem),
            Node("positive-gaps-bound", "Positive slots fit the total", "positiveGaps_card_le", "The number of slots required to be positive cannot exceed the total sum of all gap lengths.", DescribeRole.Theorem),
            Node("largest-fixed-surjection", "Every largest-fixed avoider is decorated", "exists_twelveData_of_largest_fixed", "An avoiding word on the standard support whose largest hat-fixed value is m equals the decorated output of some TwelveData(n,m,k) with k at most n minus m.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
