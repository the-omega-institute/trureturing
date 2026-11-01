using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Apollonian;
internal sealed class CutoffSpectralBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/radsararanando2026apollonian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euclidean spectral remainder bounds for the actual finite inner-face Apollonian graphs.",
        H("Actual cutoff spectral bounds"), Blocks(
            Describe.Lean(DescribeId.Create("finite-schur-operator-bound"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds.l2_opNorm_le_schur"),
            H("Row and column bounds control the Euclidean operator"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/juexu2026finiteschur")),
            Blocks(Paragraph(Text("For every RCLike field K, finite row type I and finite column type J, with decidable equality on J, let A be an I by J matrix over K. If real R,C are nonnegative, every sum over j in J of the norm of A(i,j) is at most R, and every sum over i in I is at most C, then the Euclidean operator norm of A is at most sqrt(R*C). Empty row or column types are included. The norm is explicitly Matrix.Norms.L2Operator. Weighted Cauchy–Schwarz first bounds the squared action of each row, and summation uses the column bounds. The theorem is a minimal licensed port of Jue Xu's proof and is consumed by the actual Apollonian late adjacency estimate."))), DescribeRole.Theorem),
            Node("lateDirected", "The actual directed late matrix",
                "For all natural k,t, lateDirected k t is a real matrix on the actual LateVertex k t type. Its u,v entry is one exactly when the constructed graph has the edge u→v oriented from strictly younger to strictly older birth, and zero otherwise. The actual late ordinary adjacency is the sum of this matrix and its transpose.", DescribeRole.Definition),
            Node("late_adjacency_norm_le", "The actual late adjacency operator bound",
                "For every natural k,t, the Euclidean L2 operator norm of lateAdjacency k t is at most 2*sqrt(3*(3*2^(k+t-k-1))). The exponent uses natural subtraction. The outgoing row sums of the directed matrix are at most three, and its incoming column sums are at most 3*2^(k+t-k-1), by the proved constructor-derived orientation and degree laws. The Schur bound controls each direction and transposition preserves the L2 norm. Empty late sets are included. No degree or spectral estimate is assumed.", DescribeRole.Theorem),
            Node("late_adjacency_normalized_le", "Uniform bound with the original normalization",
                "For every natural cutoff k and natural t≥1, the L2 operator norm of lateAdjacency k t divided by the real power 2^((k+t)/2) is at most 3*sqrt(2)/2^(k/2). The exponents in both real powers use real division by two. The bound is uniform in the later stage t and includes odd stages. It concerns the late induced block of the actual graph, and does not itself establish the ordered second-eigenvalue limit.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("apollonian-spectral-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
