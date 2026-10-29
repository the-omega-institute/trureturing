using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class BarreseOrderedLevelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/BarreseOrderedLevels.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/barrese2023levels");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Gaussian recurrence counts literal fixed-slot source boards, with the published top-down order restored.",
        H("Prescribed Ordered Level Numbers"),
        Blocks(
            Node("barreseorderedlevels-leveltotal", "Native cell total", "levelTotal",
                "For a source board with U columns and mt rows, the p-th bottom-up level total is the sum, over j=0,...,m-1, of the number of columns whose height exceeds mp+j. This counts the actual occupied cells in that level with weight one. It places no singleton restriction on the board.", DescribeRole.Definition),
            Node("barreseorderedlevels-nativefiber", "The complete source fiber", "NativeFiber",
                "NativeFiber(m,U,a) contains every weakly increasing U-tuple of column heights from zero through m times length(a) with the prescribed bottom-to-top totals a. Every column slot, every empty top row and every zero entry is retained.", DescribeRole.Definition),
            Node("barreseorderedlevels-nativerowsequiv", "Native boards and flat row fibers", "nativeRowsEquiv",
                "The padded row-column bijection restricts to an exact bijection between NativeFiber(r+1,U,a) and the flat fiber beginning at row bound U. Each row coordinate counts literal source cells, so the restriction preserves all level totals; the inverse reconstructs every source column height.", DescribeRole.Definition),
            Node("barreseorderedlevels-native-count", "Complete bounded enumeration", "native_count",
                "For every r,U and every finite ordered list a of nonnegative totals, the number of boards in NativeFiber(r+1,U,a) is F(a,U). Thus every positive level size m is obtained with r=m-1. Evaluate G by q-Pascal, use T_a(u,v)=[q^(a-mv)]G(u-v+m-1,m-1) when v<=u and mv<=a and zero otherwise, then use F([],u)=1 and F(a::as,u)=sum_v T_a(u,v)F(as,v). The summation states range only over 0,...,U.", DescribeRole.Theorem),
            Node("barreseorderedlevels-source2023-count", "The entire fixed ambient source question", "source2023_count",
                "For every positive m, every n and every top-down vector l indexed by the n ambient levels, the exact number of weakly increasing n-slot source column tuples with heights at most mn and those level numbers is F((l_n,...,l_1),n), with r=m-1. This is the fixed n-column, n-level ambient convention of Section 2.2. The formula includes empty top levels, all-zero data, m=1, width zero through n and every infeasible vector. No reordering or multiset quotient is used. It does not enumerate the larger rook equivalence class. Together with the normalized all-width lOperator_count formula, this gives the two source conventions of prescribed ordered level enumeration.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barrese-prescribed-ordered-level-enumeration"),
                    ResolutionKind.Proved,
                    [DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/BarreseSourceNormalization.lOperator_count")]))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
