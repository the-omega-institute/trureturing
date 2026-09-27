using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfTwelveInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfTwelveInverse.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first decorated construction is injective, and avoidance gives its required normal form.",
        H("Uniqueness of the First Decorated Description"),
        Blocks(
            Node("filler-prefix", "The initial filler prefix", "takeWhile_filler_prefix", "When every entry of b fails P and the next entry a satisfies P, taking entries while P fails from b followed by a and a tail returns b.", DescribeRole.Theorem),
            Node("blocks-injective", "Uniqueness of filler blocks", "afterBlocks_injective_blocks", "For a fixed skeleton whose entries satisfy P, equally long lists of P-failing filler blocks are equal if their interleavings are equal.", DescribeRole.Theorem),
            Node("interleavings-equal", "Uniqueness with a leading block", "interleaving_blocks_eq", "If two words have the same leading skeleton entry, equal separated interleavings determine their leading filler blocks and all following filler blocks.", DescribeRole.Theorem),
            Node("after-blocks-decomposition", "Every word has an interleaving decomposition", "exists_afterBlocks_decomposition", "Each list splits into an initial P-failing block and a skeleton of P-satisfying entries, with one P-failing block after each skeleton entry.", DescribeRole.Theorem),
            Node("fixed-syntax-decomposition", "Splitting at a singleton block", "fixedSyntax_decomposition", "FixedSyntax f p yields a prefix of values below f, then f, then either no entry or an entry larger than f followed by a tail.", DescribeRole.Theorem),
            Node("upper-filter", "Recovering the upper skeleton", "twelveList_upper_filter", "Filtering a decorated output for entries above m returns its stored upper word sigma.", DescribeRole.Theorem),
            Node("blocks-equal", "Recovering inserted blocks", "twelveList_blocks_eq", "Equal decorated outputs with the same n and m have equal lists of lower filler blocks.", DescribeRole.Theorem),
            Node("raw-gaps-equal", "Recovering the gap vector", "twelveList_gap_raw_eq", "Equal decorated outputs with the same n and m have equal underlying labelled gap vectors.", DescribeRole.Theorem),
            Node("subsets-equal", "Recovering the chosen upper subset", "twelveList_K_eq", "Equal decorated outputs with the same n and m have the same selected upper subset K.", DescribeRole.Theorem),
            Node("twelve-list-injective", "Injectivity at fixed parameters", "twelveList_injective", "For fixed n, m and k, the decorated output map from TwelveData to lists is injective.", DescribeRole.Theorem),
            Node("largest-point-unique", "The largest fixed point is unique", "twelveList_m_eq", "Under the support bounds, equal decorated outputs must have the same distinguished largest fixed value m, even when their other parameters differ.", DescribeRole.Theorem),
            Node("lower-filter", "Avoidance forces the lower word", "avoiding_lower_filter", "An avoiding word on the standard support fixed at m has its entries below m in the unique decreasing order.", DescribeRole.Theorem),
            Node("first-normal-form", "Normal form of a first-pattern avoider", "avoiding_twelve_normal_form", "An avoiding word fixed at m splits into a lower prefix, m, and upper skeleton entries with lower filler blocks after them; the upper skeleton is its filter above m.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
