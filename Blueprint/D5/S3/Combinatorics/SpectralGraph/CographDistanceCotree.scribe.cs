using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class CographDistanceCotreeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/SpectralGraph/CographDistanceCotree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mannamandaltura2026cographdistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distance matrices along cotree component cuts.",
        H("Distance matrices along cotree component cuts"),
        Blocks(
            Entry("distanceMatrix", "Ordinary distance matrix",
                "Cast the native shortest-path distances to real numbers.", DescribeRole.Definition),
            Entry("ones", "All-ones matrix",
                "Every entry is one, including the diagonal.", DescribeRole.Definition),
            Entry("dist_eq", "Native distances",
                "Distinct vertices of a connected cograph have distance one on edges and two on nonedges. The diagonal is zero."),
            Entry("distanceMatrix_eq", "Distance matrix identity",
                "The ordinary distance matrix is 2J − 2I − A."),
            Entry("localMatrix", "Local shifted matrix",
                "The local matrix is (2−q)J − (x+2)I − A on the induced graph at shift x and parent label q.", DescribeRole.Definition),
            Entry("localMatrix_root", "Shifted root distance matrix",
                "At q=0 on a connected cograph the local matrix is the shifted ordinary distance matrix."),
            Entry("localMatrix_induce", "Restriction to a child",
                "Restricting the local matrix to an induced carrier uses the same shift and label with the child adjacency matrix."),
            Entry("label", "Numerical labels",
                "One represents a join and two represents a union.", DescribeRole.Definition),
            Entry("componentEquiv", "Coordinates for component cuts",
                "Each vertex corresponds to a component of the cut and a vertex in its support.", DescribeRole.Definition),
            Entry("localMatrix_node", "Block expression",
                "The parent matrix consists of the child blocks and the all-ones update with coefficient given by the label difference."),
            Entry("localOperator", "Local linear operator",
                "View the local matrix as an endomorphism of the real Euclidean space of native vertices.", DescribeRole.Definition),
            Entry("oneVector", "All-ones vector",
                "All coordinates are one.", DescribeRole.Definition),
            Entry("pairing_oneVector", "Pairing with all ones",
                "Pairing with the all-ones vector sums the coordinates."),
            Entry("localOperator_symmetric", "Symmetry of the local operator",
                "The adjacency matrix is symmetric, as are the identity and all-ones terms."),
            Entry("componentCoordinates", "Euclidean component coordinates",
                "Separate the native Euclidean space into a product indexed by cut components.", DescribeRole.Definition),
            Entry("localOperator_node", "Rank-one update at a node",
                "In component coordinates apply the child block operator and a rank-one update in the direction of the all-ones vector."),
            Entry("localOperator_node_states", "Transport of local states",
                "Component coordinates preserve nullity, nonzero kernel pairing and scalar response under the block expression."),
            Entry("leaf_states", "Leaf states",
                "The one-dimensional leaf gives a nonzero kernel sum at its pole and a scalar response at other shifts."))));

    private static DocumentBlock Entry(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("cographdistancecotree-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
