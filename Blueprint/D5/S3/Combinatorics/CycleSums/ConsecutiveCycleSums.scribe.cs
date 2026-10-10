using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CycleSums;

internal sealed class ConsecutiveCycleSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSums.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive natural a, every sufficiently large consecutively labelled cycle can be completed using at most n/a added edges; a hub and tail construction uses fewer than the square root of 2n + 8 edges for n at least eight.",
        H("Sublinear edge completion for consecutive cycle sums"),
        Blocks(
            Node("consecutive-cycle-label", "The fixed consecutive labels", "label",
                "For every natural n and vertex v in Fin n, label v is the natural number v.val + 1. Thus the vertices have the labels one through n in their original cycle order.", DescribeRole.Definition),
            Node("consecutive-cycle-complete", "Completeness by connected vertex sums", "IsComplete",
                "For every natural n and simple graph G on Fin n, IsComplete G means that, for every natural k with 1 ≤ k ≤ n(n + 1)/2, there exists a nonempty finite vertex set C such that the subgraph of G induced by C is connected and the sum of label v over v in C equals k.", DescribeRole.Definition),
            Node("consecutive-cycle-claim", "The eventual edge budget", "claim",
                "For every natural a with 1 ≤ a, there exists a natural N such that, for every natural n with N ≤ n, there exists a simple graph G on Fin n containing cycleGraph n, for which the natural cardinality of G.edgeSet minus cycleGraph n.edgeSet, multiplied by a, is at most n, and IsComplete G holds.", DescribeRole.Definition),
            Node("consecutive-cycle-result", "The eventual edge budget holds", "result",
                "The claim holds. For n at least eight, choose the least k at least four whose triangular number is at least n + 4. Join label one to labels three through k + 1. Subsets of labels two through k realize every sum from two through the kth triangular number minus three. Adjoining label one makes these sets connected, and consecutive tail prefixes extend their sum intervals without gaps up to the nth triangular number minus two. The remaining sums one, two, the nth triangular number minus one and the nth triangular number are realized by {1}, {2}, {2, …, n} and {1, …, n}. The construction adds at most k minus one edges, with (k minus one) squared strictly less than 2n + 8. For every positive a, the threshold max(8, 4a squared) ensures that the number of added edges multiplied by a is at most n.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("marotti-needleman-2026-consecutive-cycle-sums"),
                    ResolutionKind.Proved))
        ),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsGraph"))]));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
