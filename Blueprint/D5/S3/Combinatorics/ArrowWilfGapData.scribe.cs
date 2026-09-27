using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfGapDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfGapData.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak compositions record where lower entries are inserted around a permutation skeleton.",
        H("Gap Vectors and Interleaved Words"),
        Blocks(
            Node("labelled-gaps", "Labelled weak compositions", "GapsOn", "GapsOn(iota,t) is the finite type of nonnegative vectors indexed by iota whose entries sum to t.", DescribeRole.Definition),
            Node("linear-gaps", "Linear weak compositions", "Gaps", "Gaps(r,t) specializes labelled gap vectors to the index set Fin(r).", DescribeRole.Definition),
            Node("gap-list", "List of gap lengths", "gapList", "Reading a vector in the standard order of Fin(r) gives its list of r nonnegative parts.", DescribeRole.Definition),
            Node("positive-labelled-gaps", "Positive prescribed gaps", "PositiveGapsOn", "This subtype requires each gap indexed by R to have positive length while the total length remains t.", DescribeRole.Definition),
            Node("positive-linear-gaps", "Positive linear gaps", "PositiveGaps", "PositiveGaps(r,t,R) is the linear-index specialization of PositiveGapsOn.", DescribeRole.Definition),
            Node("gap-indicator", "Mandatory units", "gapIndicator", "The indicator vector has value one on R and zero at every other gap label.", DescribeRole.Definition),
            Node("positive-gap-equivalence", "Removing mandatory units", "positiveGapsEquiv", "When the cardinality of R is at most t, subtracting one in every prescribed slot identifies positive gaps of total t with ordinary gaps of total t minus the cardinality of R.", DescribeRole.Definition),
            Node("gap-at", "A gap following a value", "gapAt", "The gap following a support value x is read from the label some x, and is zero outside the support.", DescribeRole.Definition),
            Node("gap-sizes", "Gap lengths in skeleton order", "gapSizes", "The gap list begins with the leading gap and then reads the remaining labels in the order of a word on the upper support.", DescribeRole.Definition),
            Node("gap-sizes-length-sum", "Length and total of gap sizes", "gapSizes_length_sum", "The list of gaps has one more entry than the support has values, and the sum of its entries is t.", DescribeRole.Theorem),
            Node("after-blocks", "Interleaving after skeleton entries", "afterBlocks", "The first filler block follows the first skeleton value, the second follows the second, and so on; extra blocks are ignored once the skeleton ends.", DescribeRole.Definition),
            Node("after-blocks-permutation", "Interleaving preserves the values", "afterBlocks_perm", "With equal numbers of blocks and skeleton entries, the interleaved word permutes the skeleton followed by all flattened blocks.", DescribeRole.Theorem),
            Node("filter-skeleton", "Recovering the skeleton", "filter_afterBlocks_skeleton", "If the predicate holds on all skeleton entries and no filler entry, filtering the interleaving by the predicate returns the skeleton.", DescribeRole.Theorem),
            Node("filter-fillers", "Recovering the fillers", "filter_afterBlocks_fillers", "Under the same separation of skeleton and filler entries, filtering by the complement of the predicate returns the flattened filler blocks.", DescribeRole.Theorem),
            Node("small-prefix-syntax", "A lower prefix preserves singleton syntax", "fixedSyntax_append_small_iff", "A prefix whose values all lie below g does not change FixedSyntax g for a suffix that contains g.", DescribeRole.Theorem),
            Node("interleaved-fixed-syntax", "A low filler destroys a singleton block", "fixedSyntax_afterBlocks_iff", "For a skeleton with distinct entries and filler entries below g, g has singleton syntax after interleaving exactly when it had singleton syntax in the skeleton and its following filler block is empty.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
