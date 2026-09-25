using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfTwentyThreeInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second decorated description is a bijection with the nonexceptional smallest-fixed-point fiber.",
        H("Inverting the Second Decorated Construction"),
        Blocks(
            Node("minimum-avoiders", "The smallest-fixed-point fiber", "MinAvoiders", "The subtype consists of avoiding words on the standard support fixed at m and with no fixed value below m.", DescribeRole.Definition),
            Node("minimum-avoider-of-data", "Decorated data land in the fiber", "minAvoiderOfData", "When one at most m less than n, a TwentyThreeData object yields an avoider whose smallest hat-fixed value is m.", DescribeRole.Definition),
            Node("minimum-normal-form", "Normal form of a smallest-fixed avoider", "minAvoider_normal_form", "Every such avoider splits into a lower prefix, m, and the decreasing upper skeleton with lower filler blocks after each upper entry.", DescribeRole.Theorem),
            Node("prefix-no-fixed", "The lower prefix has no fixed point", "normal_prefix_no_fixed", "The lower prefix of the normal form has no hat-fixed value among its entries.", DescribeRole.Theorem),
            Node("normal-support-split", "Partition of lower support", "normal_support_split", "The flattened fillers form a subset of the lower support, the prefix set is its complement there, and both lower lists have distinct entries.", DescribeRole.Theorem),
            Node("normal-lower-words", "The recovered lower words", "normal_lower_words", "The normal prefix is a word with no fixed point on its support, and the flattened filler blocks form a word on the complementary lower support.", DescribeRole.Theorem),
            Node("upper-gaps-of-blocks", "Recover the upper gap vector", "upper_gaps_of_blocks", "A block list aligned with the decreasing upper skeleton determines an upper-labelled gap vector whose readout is the list of block lengths.", DescribeRole.Theorem),
            Node("minimum-surjective", "Every smallest-fixed avoider is decorated", "minAvoider_surjective", "Every avoiding word in the nonexceptional fiber equals the output of some TwentyThreeData(n,m,r).", DescribeRole.Theorem),
            Node("filler-prefix-unique", "A leading filler block is unique", "filler_prefix_unique", "When two separated words meet at the same first skeleton entry, equality determines both leading filler blocks and remaining tails.", DescribeRole.Theorem),
            Node("after-blocks-unique", "The upper filler blocks are unique", "afterBlocks_unique", "For a fixed skeleton separated by a predicate from its fillers, equality of interleaved outputs forces equality of aligned filler-block lists.", DescribeRole.Theorem),
            Node("upper-gaps-injective", "Gap lengths determine their vector", "upperGapSizes_injective", "Two gap vectors on the same upper support and with the same ordered upper gap lengths are equal.", DescribeRole.Theorem),
            Node("split-member-unique", "A split at a unique value is unique", "split_at_member_unique", "If m is absent from both prefixes, equal words split at m have equal prefixes and suffixes.", DescribeRole.Theorem),
            Node("data-normal-bounds", "Bounds for decorated normal forms", "data_normal_bounds", "The decorated prefix lies below m, the filler-block count matches the upper skeleton, every filler lies below m, and the flattened blocks recover rho.", DescribeRole.Theorem),
            Node("twenty-three-list-unique", "Uniqueness of decorated data", "twentyThreeList_unique", "Equal outputs with the same n and m have equal r and heterogeneously equal decorated data.", DescribeRole.Theorem),
            Node("twenty-three-family", "The full decorated fiber", "TwentyThreeFamily", "The family is the dependent sum of TwentyThreeData(n,m,r) over r less than m.", DescribeRole.Definition),
            Node("twenty-three-family-map", "Map the family to the fiber", "twentyThreeFamilyMap", "Each object in the dependent decorated family maps to its avoiding word with smallest fixed point m.", DescribeRole.Definition),
            Node("twenty-three-family-equivalence", "The nonexceptional bijection", "twentyThreeFamilyEquiv", "For positive m below n, the complete decorated family is equivalent to the avoidance fiber with smallest fixed point m.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
