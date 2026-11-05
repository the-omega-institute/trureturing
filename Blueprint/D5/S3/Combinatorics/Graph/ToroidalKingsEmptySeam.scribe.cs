using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ToroidalKingsEmptySeamDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/ToroidalKingsEmptySeam.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite free and toroidal king configurations, their coefficients, and square tilings.",
        H("King boards, empty seams and square tilings"),
        Blocks(
            Paragraph(Text("OEIS A394697 uses the maximum coefficient of the independence polynomial of the full square torus. A063443 counts square tilings by unit and two-by-two squares and records their correspondence with free king boards of side one less. The free entropy and maximum-versus-total mechanisms are credited to Calkin, James and Purvis, Counting Kings, and Liang, arXiv:2505.12776v2, Proposition 3.1. The toroidal seam comparison retains both periodic coordinates and every integer side length.")),
            Node("gap", "gap", "Absolute coordinate difference", "gap(a,b) is (a-b)+(b-a) in natural arithmetic, hence the usual absolute difference."),
            Node("free-adjacency", "freeAdjacent", "Free king adjacency", "Two distinct coordinate pairs are adjacent when both coordinate gaps are at most one."),
            Node("torus-adjacency", "torusAdjacent", "Periodic king adjacency", "Two distinct coordinate pairs are adjacent when min(gap,n-gap) is at most one in both coordinates. The board bounds put both coordinates in zero through n minus one."),
            Node("seam-adjacency", "empty_seam_adjacency", "An empty row and column remove wraparound edges", "For every natural n and coordinate pairs u and v whose four coordinates are less than n-1, toroidal adjacency is equivalent to free adjacency. The statement includes odd n and has no parity premise.", DescribeRole.Theorem),
            Node("board", "board", "The square vertex set", "board(n) is the Cartesian product of two copies of Finset.range n."),
            Node("independent-subsets", "independentSets", "The finite configuration family", "Filter the powerset of the specified finite board by the requirement that no ordered pair of its vertices is adjacent. The distinctness condition in king adjacency permits the empty configuration and does not create loops."),
            Node("free-count", "freeCount", "Free square configurations", "freeCount(n) counts all independent subsets of the free n by n king board."),
            Node("rectangle-count", "rectangleCount", "Free rectangular configurations", "rectangleCount(r,c) counts all independent subsets of range r times range c with free king adjacency."),
            Node("torus-count", "torusCount", "Toroidal total count", "torusCount(n) counts all independent subsets of the full n by n toroidal king graph."),
            Node("coefficient", "coefficient", "Cardinality coefficient", "coefficient(n,k) is the number of toroidal independent sets of cardinality k, including zero coefficients and k=0."),
            Node("peak", "peak", "The A394697 maximum", "peak(n) is the natural supremum of coefficient(n,k) for all k from zero through n squared, inclusive."),
            Node("lower-seam-bound", "free_le_torus", "Injecting the smaller free board", "For every natural n, freeCount(n-1) is at most torusCount(n). The same vertex subset is embedded with the final row and column empty.", DescribeRole.Theorem),
            Node("upper-free-bound", "torus_le_free", "Forgetting periodic edges", "For every natural n, torusCount(n) is at most freeCount(n). Every toroidal independent set is a free independent set on the same vertices.", DescribeRole.Theorem),
            Node("peak-loss", "count_le_mul_peak", "Polynomial loss from taking the maximum", "For every natural n, torusCount(n) is at most (n squared plus one) times peak(n). The configuration family is partitioned by all n squared plus one possible cardinalities.", DescribeRole.Theorem),
            Node("peak-upper", "peak_le_count", "A coefficient is bounded by the total", "For every natural n, peak(n) is at most torusCount(n).", DescribeRole.Theorem),
            Node("large-tile", "squareTile", "A two-by-two tile", "squareTile(u) consists of the four cells with each coordinate equal to the corresponding coordinate of u or its successor."),
            Node("tiling-placements", "tilingPlacements", "Square tilings with implicit unit completion", "For side m, choose lower-left coordinates in board(m-1) for pairwise disjoint two-by-two tiles. Every uncovered cell has its uniquely determined unit tile. This is an encoding of complete tilings, with no additional independent choices for unit tiles."),
            Node("tiling-count", "a063443", "The literal A063443 count", "a063443(m) is the cardinality of the square-tiling placement family. Its free-board side is m minus one, as stated by OEIS A063443."),
            Node("full-tiling", "tilingBlocks", "Recovering the full tile collection", "Take all selected squareTile blocks and one singleton tile for every cell of board(m) outside their union."),
            Node("tiling-king-identity", "tiling_free_identity", "The exact source index shift", "For every natural m, a063443(m)=freeCount(m-1). Two two-by-two tiles overlap exactly when both lower-left coordinate gaps are at most one; their distinct anchors therefore have exactly free king adjacency.", DescribeRole.Theorem),
            Node("free-square-entropy", "free_log_limit", "Existence of the free square entropy", "There exists a nonnegative real s such that log(freeCount(n))/n squared converges to s through all natural n. Restricting at a straight cut proves rectangular submultiplicativity. Transposition gives symmetry, the empty configuration gives positivity, and all vertex subsets give the binary area bound. The rectangular entropy theorem supplies the square limit without assuming it.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string name, string title, string prose,
        DescribeRole role = DescribeRole.Definition) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
        StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);
}
