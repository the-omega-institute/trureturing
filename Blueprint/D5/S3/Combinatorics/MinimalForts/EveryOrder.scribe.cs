using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class EveryOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/EveryOrder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive order and the full successive ratio", H("Every positive order and the full successive ratio"),
        Blocks(
            Node("finite-graph", "Actual finite simple graph", "FiniteGraph", "An object consists of an actual vertex type with a Fintype enumeration, decidable equality, a SimpleGraph on that type and decidable adjacency. SimpleGraph imposes symmetry and excludes loops; there are no weights. The empty vertex type is permitted by the structure.", DescribeRole.Definition),
            Node("count", "The full minimal-fort count", "FiniteGraph.count", "For every FiniteGraph A, count(A) is the cardinality of minimalForts(A.graph). It filters every actual vertex subset by the reused nonempty fort predicate and inclusion-minimality over all fort subsets. It counts neither equivalence classes nor a chosen subclass.", DescribeRole.Definition),
            Node("result", "Every positive order and the full successive ratio", "result", "There exists a sequence of actual finite simple undirected loopless unweighted graphs indexed by every natural n. For every positive n the vertex count is exactly n, the graph is connected, and its entire minimal-fort count A(n) is positive. Along the entire sequence n tending to infinity, A(n)/(3/2)^n tends to one and A(n+1)/A(n) tends to three halves. The real cube root of three is strictly less than three halves, which is strictly less than two. The first two positive orders use complete graphs. For n at least three, write n-3=6k+r with 0<=r<6 and use the mixed graph from the feasible sequence for residue r. Simultaneous convergence over all six residues gives the full limit, rather than only a block subsequence or a limit superior. The successive-ratio limit follows from the normalization and positivity. This proves the mathematical existence and ratio assertion of arXiv:2404.05963v1, Section 6, Conjecture 31, with the additional every-order and connectedness requirements. The source sentence itself does not separately impose vertex count n at index n.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
