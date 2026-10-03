using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CrosswordGrid;

internal sealed class SkewMergedRookRegionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookRegions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A graph without the three forbidden induced configurations splits into a clique and an independent set, and skew-merged permutations are exactly the 2143- and 3412-avoiders.",
        H("Split Graphs and Forbidden Permutation Patterns"),
        Blocks(
            Node("skew-merged-rook-regions-graph-split-criterion", "A clique and an independent set", "graph_split_criterion",
                "Let n be positive and let G be a simple graph on zero through n minus one. Suppose that G has no induced subgraph consisting of two disjoint edges, no induced four-cycle and no induced five-cycle. There is a set of vertices forming a clique such that no two vertices outside that set are adjacent.", DescribeRole.Theorem),
            Node("skew-merged-rook-regions-skew-iff-avoidance", "Avoiding 2143 and 3412", "skew_iff_avoidance",
                "For positive n, a permutation w is skew-merged if and only if it avoids the classical patterns 2143 and 3412. Explicitly, for every four positions a less than b less than c less than d, neither w(b) less than w(a) less than w(d) less than w(c) nor w(c) less than w(d) less than w(a) less than w(b) holds.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
