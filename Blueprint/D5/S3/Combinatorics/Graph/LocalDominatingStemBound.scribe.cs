using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LocalDominatingStemBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LocalDominatingStemBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The average order of dominating sets containing a stem satisfies the sharp bound (4n+1)/6.",
        H("The local average at a stem"),
        Blocks(
            Node("local-stem-claim", "Chen–He–Lai–Li Conjecture 6.1", "claim",
                "For every finite simple graph G of order n at least two without isolated vertices, "
                    + "every vertex v with exactly l leaf neighbours, where l is at least one, satisfies "
                    + "avdAt(G,v) at most (4n+1)/6. Equality holds exactly when l=1 and G is star-like. "
                    + "This is Conjecture 6.1 of Tingyun Chen, Weihua He, Hong-Jian Lai and Jianping Li, "
                    + "On the local average order of dominating sets, arXiv:2610.11446v1.",
                DescribeRole.Definition),
            Node("local-stem-result", "The sharp bound and equality case", "result",
                "Remove v and its l leaves, leaving an isolate-free graph H of order h=n-l-1. "
                    + "Write A for the family internally dominating all vertices of H not adjacent to v, "
                    + "and B for all dominating sets of H. The conditioned mean is 1+l/2+mean(A). "
                    + "When A=B the Beaton–Cameron bound applies directly. Otherwise, connect r copies "
                    + "of H through a hub with one pendant leaf. Its exact dominating-set counts give "
                    + "a power-versus-linear inequality, contradicted at r=4hb²+2 if mean(A) is at least "
                    + "2h/3, where b is the size of B. Thus mean(A) is at most 2h/3, with equality "
                    + "forcing A=B. Numerical equality forces l=1. The global equality characterization "
                    + "of Beaton and Cameron then identifies G as star-like. Conversely, in a star-like "
                    + "graph each residual neighbour of v retains a leaf, so A=B, and the global "
                    + "mean identity gives the required local equality.",
                DescribeRole.Theorem
                , new OpenProblemResolutionClaim(ProblemSlugRef.Create("chen-he-lai-li-2026-local-average-dominating-stem"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
