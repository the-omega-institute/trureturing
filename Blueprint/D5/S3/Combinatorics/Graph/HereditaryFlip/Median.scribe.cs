using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HereditaryFlip;

internal sealed class MedianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HereditaryFlip/Median.";
    private static readonly LibraryNoteRef Classical =
        LibraryNoteRef.Create("D5/L/GraphInvariants/betre2024pure");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native metric medians in hereditary finite-support flip graphs are coordinate "
            + "majorities. Such a graph is a median graph precisely when its family contains "
            + "the empty face and is flag.",
        H("Native metric medians and flag families"),
        Blocks(
            Paragraph(Text("Let V be any type with decidable equality and let K be a set of "
                + "finite subsets of V. Neither V nor K needs to be finite. The flip graph has "
                + "vertices S in K, with adjacency given by a symmetric difference of size one. "
                + "The results assume IsLowerSet K: every subset of a legal support is legal. "
                + "The native graph distance is the length of a shortest actual graph walk; "
                + "the hereditary geodesic construction establishes reachability before its use.")),
            Entry("median-condition", "IsMedian", "Three native distance intervals",
                "For any SimpleGraph G and vertices A, B, C and M, IsMedian G A B C M is "
                    + "the conjunction of dist(A,M) + dist(M,B) = dist(A,B), "
                    + "dist(B,M) + dist(M,C) = dist(B,C), and "
                    + "dist(C,M) + dist(M,A) = dist(C,A). Every distance here is G.dist. "
                    + "The condition itself imposes no connectedness; it is used together "
                    + "with connectedness in the graph property below.", DescribeRole.Definition),
            Entry("median-graph", "IsMedianGraph", "Connectedness and a unique median",
                "IsMedianGraph G means that G is connected and, for every triple of vertices "
                    + "A, B and C, there exists exactly one vertex M satisfying IsMedian G A B C M. "
                    + "Connectedness includes a nonempty vertex type. This is a graph metric "
                    + "condition with an existence and uniqueness requirement.", DescribeRole.Definition),
            Entry("reconstruction", "is_median_iff", "The intervals reconstruct the support",
                "For hereditary K and any four vertices A, B, C and M of its flip graph, "
                    + "IsMedian (flipGraph K) A B C M holds if and only if the support of M equals "
                    + "the union of A intersect B, B intersect C, and C intersect A. The interval "
                    + "criterion forces M to include every coordinate present in any two inputs. "
                    + "Conversely, its three upper inclusions exclude a coordinate present in "
                    + "at most one input: among the three pairs there is a pair omitting it. "
                    + "Thus the support is exactly the majority. The majority satisfies all "
                    + "six inclusions by the same coordinate calculation. Any two common "
                    + "interval vertices therefore have equal supports and are equal as "
                    + "vertices. This statement identifies a candidate median; its membership "
                    + "in K is essential for existence.", DescribeRole.Theorem),
            Entry("classification", "median_graph_iff_flag", "Median graphs classify flag families",
                "For every hereditary K, IsMedianGraph (flipGraph K) is equivalent to the "
                    + "conjunction of empty-set membership in K and Flag K. Here Flag K says "
                    + "that every finite support S whose subsets of cardinality at most two "
                    + "belong to K also belongs to K. Empty and singleton subsets are included "
                    + "in this test. Starting from a median graph, a vertex supplies the empty "
                    + "face by heredity. The reconstructed support of each median proves "
                    + "majority closure; the majority/flag equivalence then proves flagness. "
                    + "Starting from empty-set membership and flagness, the graph is connected "
                    + "by deletion and insertion walks. Majority closure supplies the legal "
                    + "majority vertex for each triple, and reconstruction proves it is the "
                    + "unique median. No maximal-face or ambient-finiteness hypothesis is used. "
                    + "An absent singleton remains absent, so no ghost vertices are added. "
                    + "The empty family is flag but its empty graph fails connectedness; the "
                    + "family consisting only of the empty face gives a one-vertex median graph. "
                    + "The finite complex characterization is classical, as in Xie and Xu, "
                    + "Characterizing simplex graphs, Theorem 1.5.", DescribeRole.Theorem),
            H("Independent sets and Fibonacci supports"),
            Paragraph(Text("For any simple graph H on V, take K to consist of its finite "
                + "independent sets, using Mathlib's H.IsIndepSet on the underlying sets. "
                + "Independence is hereditary and the empty set is independent. If all pairs "
                + "inside a support S are independent, no two distinct elements of S are "
                + "adjacent in H, so S is independent. This verifies Flag K and applies "
                + "median_graph_iff_flag to its one-coordinate flip graph. Its native median "
                + "is the coordinate majority, and Metric.dist_eq gives distance equal to "
                + "the size of the symmetric difference.")),
            Paragraph(Text("In particular, on Fin n take H to be the path whose adjacent "
                + "positions differ by one. Its independent supports are exactly the subsets "
                + "with no consecutive positions. Sending a support to its Boolean indicator "
                + "identifies these supports with length-n Fibonacci words without consecutive "
                + "ones; insertion or deletion changes one bit. Thus the support version of "
                + "the Fibonacci cube has the native median property, with median given by "
                + "bitwise majority. This consequence concerns the support graph. A graph "
                + "isomorphism to any separately defined Boolean-word graph requires its own "
                + "interface proof; it is not asserted here.")),
            H("The boundary of a triangle"),
            Paragraph(Text("All proper subsets of a three-element set form a hereditary "
                + "family. Its flip graph has native symmetric-difference distance, yet the "
                + "three two-element faces have no median: their coordinate majority is the "
                + "missing three-element face. Heredity and the isometric distance formula "
                + "alone therefore do not imply the median property."))),
        []));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("hereditary-flip-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Classical),
            Blocks(Paragraph(Text(prose))), role);
}
