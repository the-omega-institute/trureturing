using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class BarreseSourceNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/barrese2023levels");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive left-to-right column tuples give an explicit all-width source carrier for the l-operator.",
        H("The Normalized Source l-Fiber"),
        Blocks(
            Node("barresesourcenormalization-positivecolumns", "Normalized source tuples", "PositiveColumns",
                "A normalized source board is a finite weakly increasing list of strictly positive column heights. Deleting leading zero columns from the padded source tuple gives this representative. The empty list represents the empty board. Width and height are both unrestricted in this carrier.", DescribeRole.Definition),
            Node("barresesourcenormalization-normalizedcolumnsequiv", "Finite diagrams and positive source columns", "normalizedColumnsEquiv",
                "Transpose a finite Young diagram, take its positive row-length list, then reverse that list to obtain the source left-to-right column heights. The inverse reverses a positive source tuple, forms its Young diagram and transposes. The existing positive row-length equivalence proves that the two maps are inverse. This fixes normalization and right alignment.", DescribeRole.Definition),
            Node("barresesourcenormalization-columnlevel", "Literal cells in a normalized source level", "columnLevel",
                "The p-th bottom-up level total is the sum over its m rows of the number of positive source column heights exceeding the absolute row index mp+j. The column/diagram correspondence preserves these literal cell totals in every level, including all levels above the board.", DescribeRole.Definition),
            Node("barresesourcenormalization-lfiber", "Exact l-operator data", "LFiber",
                "LFiber(m,c) consists of every positive source column tuple whose bottom-up totals are the reverse of c and zero thereafter, with every entry of c strictly positive. For nonempty c this is exactly the trimmed top-down tuple in Definition 4 of Barrese, Loehr, Remmel and Sagan, arXiv:1508.05944v1: each displayed level is nonempty and every higher one is empty. An explicit zero in a nonempty target tuple is rejected. The empty-board extension used here is l(empty)=[], which is stated separately because that definition does not define its largest nonempty level.", DescribeRole.Definition),
            Node("barresesourcenormalization-source2015-count", "The entire normalized all-width source count", "source2015_count",
                "For every positive m and every finite target tuple c, the cardinality of LFiber(m,c) is zero if c has a nonpositive entry; otherwise it is F(reverse(c),last(c)), with the empty-list bound taken as zero. The original singleton targets are included, while the unknown input boards are unrestricted Ferrers boards. The source-to-diagram and derived-padding bijections establish this formula for all widths and all allowed heights. For a singleton target with t positive entries, the uppermost level is nonempty, so heights range from m(t-1)+1 through mt.", DescribeRole.Theorem),
            Node("barresesourcenormalization-loperator", "The native trimmed l-operator", "lOperator",
                "Start with the literal bottom-up level cell totals. These totals decrease weakly, and finiteness of the board supplies an empty level. Let t be the first empty level index. The operator reverses the list of totals at indices zero through t-1. Thus t is exactly the largest nonempty level in the source's one-based numbering, and the empty board has the stated empty-tuple extension.", DescribeRole.Definition),
            Node("barresesourcenormalization-operatorfiberequiv", "Exact operator fiber correspondence", "operatorFiberEquiv",
                "The native equality lOperator(m,B)=c is equivalent to the absolute-level specification LFiber(m,c). The forward map uses positivity before the first zero and vanishing afterwards. The reverse map uses uniqueness of a positive finite list from its zero-extended entries: neither an appended zero nor a reordered tuple can represent the same data.", DescribeRole.Definition),
            Node("barresesourcenormalization-loperator-count", "Evaluation of the native l-operator fiber", "lOperator_count",
                "For every positive m and every c, the number of arbitrary-width positive source column tuples B satisfying lOperator(m,B)=c is the same guarded Gaussian recurrence as source2015_count. No width bound is supplied as a premise: last(c), or zero for the empty list, is derived from the bottom-level total. This is the prescribed l-fiber count of Section 6.2 of arXiv:1508.05944v1 under normalized source-column notation. Counting all possible horizontal translations in an unbounded absolute grid is a different carrier; in the fixed 2023 rectangle all literal column positions remain fixed instead.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
