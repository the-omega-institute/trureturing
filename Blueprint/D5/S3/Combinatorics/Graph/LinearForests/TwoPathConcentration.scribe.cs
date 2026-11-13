using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class TwoPathConcentrationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two actual B-ended paths concentrate on the complete original labelled bipartition with an exact six-vertex residual and a signed-Catalan shift.",
        H("Concentrating two paths on the original bipartition"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-disjoint-sum-configurations"),
                DeclarationHandle.Create(Prefix + "configurations_sum"),
                H("Configurations of disjoint graph sums"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary graphs G and H and finite domains V and W, every independent "
                    + "subset of their tagged disjoint sum is uniquely the disjoint union of an "
                    + "independent subset of V and an independent subset of W. This is equality "
                    + "of actual configuration families, with both empty subsets included."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-disjoint-sum-partition"),
                DeclarationHandle.Create(Prefix + "partition_sum"),
                H("Weighted partitions multiply"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For weights in any commutative semiring, the native partition of a disjoint "
                    + "graph sum is the product of the native partitions on the two original domains. "
                    + "Each weight is restricted along the corresponding tagged vertex inclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-concentration"),
                DeclarationHandle.Create(Prefix + "actual_two_path_concentration"),
                H("The actual graph move and its exact Catalan difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The finite carrier is arbitrary. Its original disjoint independent parts A and B cover every vertex. ActualTwoPaths gives a complete adjacency correspondence with paths of orders 2p+1 and 2q+1 and the given induced graph on R. It fixes every R label and gives one original B endpoint of each path. A compiled path-colouring argument derives that the original A vertices occupy odd positions and the B vertices occupy even positions from independence, disjointness, and coverage. Both p and q are at least one.")),
                    Paragraph(Text("The move isolates the last B vertex of the first path. Its remaining prefix has 2p vertices and is concatenated with the whole second path. The resulting path has 2p+2q+1 vertices. The new graph has the same full carrier and the same pointwise A and B labels. Its coordinates describe every edge, including the absence of edges between these path components and R; all R relations are unchanged.")),
                    Paragraph(Text("Independent configurations of a disjoint graph sum decompose into pairs of actual configurations by disjoint union. Their cardinalities add, and the empty configurations remain included. Exact graph relabeling then transports the entire configuration families to the given original labels. Weighted partition sums multiply along this decomposition, so the arbitrary graph R contributes exactly once.")),
                    Paragraph(Text("The residual keeps the first 2p-2 original vertices of the first path, the first 2q-2 original vertices of the second path, and every vertex of R. Its adjacency is the induced original adjacency. The embedding and the cardinality equation show that precisely six original vertices were removed; no residual vertices are added.")),
                    Paragraph(Text("For every m at least the full original cardinality, Phi at m before the move minus Phi at m after the move equals Phi at m-3 on this actual residual. The proof applies the original path-series recurrence to the configuration factorization and extracts coefficients after multiplication by the integer Catalan series. The six-vertex cardinality equation supplies all natural-subtraction bounds, including the case m equal to the full cardinality.")),
                    Paragraph(Text("The equality allows an arbitrary graph on R, including nonforests. Nonnegativity of the difference follows only when the actual induced residual is acyclic and every residual degree is at most two, by the finite-forest Catalan theorem. The statement includes empty tails when either parameter equals one, two empty tails when both equal one, empty R, original isolates, and arbitrary actual relabelings. It makes no global extremum or native-capacity assertion."))),
                DescribeRole.Theorem)), []));
}
