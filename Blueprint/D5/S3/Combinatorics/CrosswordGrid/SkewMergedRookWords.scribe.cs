using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CrosswordGrid;

internal sealed class SkewMergedRookWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The words of a permutation grid are determined by the sides of its black cells, and every complete placement has the same cardinality.",
        H("Words and Symmetries of Permutation Grids"),
        Blocks(
            Node("skew-merged-rook-words-word-structure", "Horizontal words and vertical word labels", "word_structure",
                "Let n be positive and w a permutation of zero through n minus one. Two white cells share a horizontal word exactly when they have the same row and lie on the same side of that row's black cell. There is a word representation whose vertical word label at (i, j) is twice j when i is less than the position of value j in w, and twice j plus one otherwise.", DescribeRole.Theorem),
            Node("skew-merged-rook-words-placement-card", "The size of a complete placement", "placement_card",
                "For positive n, every complete rook placement of the permutation grid of w contains exactly twice n minus two cells.", DescribeRole.Theorem),
            Node("skew-merged-rook-words-record-prefix-forces-neighbor", "Forced cells along a record prefix", "record_prefix_forces_neighbor",
                "Let n be positive, w a permutation, R a complete placement and b a nonnegative integer. Suppose that every column j less than b has its black cell either above all black cells in later columns less than b or below all of them. Whenever k plus one equals j and j is less than b, R contains the cell in column k and in the row of the black cell in column j.", DescribeRole.Theorem),
            Node("skew-merged-rook-words-symmetries", "Transposition and reflections", "symmetries",
                "For positive n, inverting a permutation, complementing its values, or reversing its positions preserves both its rook-placement count and the property of being skew-merged. Transposing every cell of a complete placement gives a complete placement for the inverse permutation. Reflecting its columns gives a complete placement for the value complement, and reflecting its rows gives a complete placement for the position reversal.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
