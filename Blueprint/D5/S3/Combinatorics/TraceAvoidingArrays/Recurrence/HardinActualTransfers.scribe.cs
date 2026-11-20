using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinActualTransfersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinActualTransfers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full transfer matrices for the diagonal and square strip graphs.",
        H("Actual strip states and their continuations"),
        Blocks(
            Node("column-transfer", "C", "Unrestricted column transfer", DescribeRole.Definition,
                "For every h≥0, C h acts on all functions from Fin(h+1) to Fin 3. The entry at current column p and successor q is one exactly when p and q differ across each horizontal bond and both diagonals. There are no within-column bonds."),
            Node("proper-word", "Word", "Proper word states", DescribeRole.Definition,
                "For every k≥0, the states are length k+1 words in Fin 3 whose adjacent labels differ. There are 3·2^k such words."),
            Node("word-transfer", "wordTransfer", "Diagonal and square row transfers", DescribeRole.Definition,
                "Both matrices act on Word k. The diagonal matrix R has entry one exactly when the two opposite diagonals differ at each pair of adjacent positions. The square matrix S has entry one exactly when vertically aligned labels differ. Horizontal edges are enforced by the state type."),
            Node("column-power", "column_power", "All column powers", DescribeRole.Theorem,
                "At every h,m≥0 and current column p, (C h)^m applied to the all-one vector equals the existing columnV m p. The zero-step vector has value one at every column. The successor step sums over the exact cross-bonds."),
            Node("column-continuations", "column_continuations", "The number of literal column tails", DescribeRole.Theorem,
                "For every fixed current column and every m≥0, the power vector entry is the number of m-column tails satisfying the immediate cross-bond conditions. The existing column reconstruction supplies the correspondence."),
            Node("column-count", "column_count", "Counting the actual strip by columns", DescribeRole.Theorem,
                "For every h,m≥0, summing the vector for m transitions gives the labelled three-colour count of the diagonal strip with height h+1 and width m+1. At width one the graph has no edges and all 3^(h+1) columns contribute."),
            Node("word-continuations", "word_continuations", "The number of literal row tails", DescribeRole.Theorem,
                "For either bond rule, every k,m≥0 and fixed proper row p, the power vector entry counts all m-row tails with the required horizontal and inter-row bonds. Every legal successor is one proper word and contributes once."),
            Node("word-count", "word_count", "Counting the actual strip by rows", DescribeRole.Theorem,
                "For both bond rules and every k,m≥0, sum the power vector indexed by all proper words. The result counts labelled three-colourings of the strip with width k+1 and height m+1. The source uses the diagonal matrix for widths at least two and the square matrix at widths two and three."),
            Node("class-powers", "row_fibres_iff_pow_mulVec", "Pullback of a quotient power", DescribeRole.Theorem,
                "Let T and Q be integer matrices on finite state sets A and B and let c map A to B. The row total of T at a over the fibre of b is Q(c(a),b) for every a and b if and only if T^m(v∘c)(a) = (Q^m v)(c(a)) for every integer vector v on B, exponent m≥0, and a in A. For the forward direction regroup the sum into fibres at each step. For the reverse direction take m=1 and let v be the indicator of b."),
            Node("lag-relation", "IsLagRelation", "Lag convention", DescribeRole.Definition,
                "For a length-d coefficient list c, the relation with shift b equates T^(b+d) on ones with the sum of c_j times T^(b+d−j) on ones for j from one through d. The manuscript uses b=1 for diagonal strip columns and b=0 for proper row words. The height-one and height-two column relations also hold at b=0."),
            Paragraph(Text("Write T(h,n) for the cardinality of the literal normalized diagonal arrays of positive height h and width n. "
                + "Read the columns in increasing order and recover the colour at (r,j) from position r of column j. "
                + "The column compatibility test compares the labels at positions r and t whenever their distance is at most one. "
                + "Reading the rows in increasing order instead recovers the colour at (r,j) from position j of row r. "
                + "Each row is a proper word, and successive rows compare the two opposite diagonals at every adjacent pair of positions. "
                + "These inverse maps give the exact graph colourings in either orientation. The unique empty tail gives the all-one vector, "
                + "and each successor step is multiplication by the same matrix, indexed by current state and then successor state.")),
            Paragraph(Text("Every diagonal strip of width at least two is connected, has an edge and is bipartite by column parity. "
                + "Horizontal edges link the vertices in each row, and each pair of successive rows is joined by a diagonal. "
                + "If L counts its labelled three-colourings, the literal normalization is 48 T(h,n) = 2^(hn)(L+6). "
                + "At width one the strip is edgeless, and 48 T(h,1) = 6^h + 3·4^h + 15·2^h.")),
            Paragraph(Text("For any of the transfer matrices M, let W_M(s) = s·1ᵀ(I−sM)⁻¹1 in the formal power series ring. "
                + "Its constant coefficient is zero, and its coefficient at degree m+1 is 1ᵀM^m1. "
                + "The coefficient matrix at degree m of the inverse is M^m, as multiplying by I−sM cancels every positive-degree coefficient. "
                + "Clearing the inverse with the polynomial adjugate gives denominator det(I−sM), whose constant coefficient is one.")),
            Paragraph(Text("At fixed h, put s = 2^h x. The row series is "
                + "T(h,1)x + (W_(C_h)(s) − 3^h s + 6s²/(1−s))/48. "
                + "The subtraction removes the contribution of all 3^h labelled first columns in degree one, and the geometric correction begins at degree two. "
                + "At fixed k ≥ 2, put s = 2^k x. The column series is (W_(R_k)(s) + 6s/(1−s))/48, "
                + "with the connected identity already applicable in degree one. "
                + "These denominators can be taken as (1−s)det(I−sM) after absorbing 1/48 into the numerator.")),
            Paragraph(Text("For width one the column series is "
                + "(6x/(1−6x) + 3·4x/(1−4x) + 15·2x/(1−2x))/48. "
                + "Each series begins in degree one and admits a polynomial denominator with constant coefficient one. "
                + "The argument applies to every fixed positive dimension.")))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
