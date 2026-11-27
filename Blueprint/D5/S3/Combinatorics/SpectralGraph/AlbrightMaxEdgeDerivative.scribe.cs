using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class AlbrightMaxEdgeDerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/albright2023kemenyedgederivative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized Laplacian edge derivative has sharp upper bound one.",
        H("The maximum normalized Laplacian edge derivative"),
        Blocks(
            Node("eigenspace", "Full normalized Laplacian eigenspace",
                AssessedProvenance.FromRepo(Source),
                "At t = 0 the frozen one-pair perturbation is the ordinary unweighted adjacency. "
                + "The frozen normalized Laplacian acts on real Euclidean vertex space. "
                + "The eigenspace is the entire kernel of L(0) minus the given eigenvalue times the identity."),
            Node("rayleighAverage", "Normalized trace on the fixed eigenspace",
                AssessedProvenance.FromRepo(Source),
                "For an orthonormal basis of the entire eigenspace with k elements, sum the fixed-vector Rayleigh forms "
                + "uᵀ L(t) u and divide by k. The vectors are fixed at t = 0. Compressing L(t) by orthogonal projection "
                + "onto this eigenspace identifies the sum with its trace at each t."),
            Node("edgeDerivative", "The derivative in Lemma 2.3",
                AssessedProvenance.FromLiterature(Source),
                "Lemma 2.3, equation (2.3), averages over the k elements of an orthonormal basis for the eigenvalue λ. "
                + "For a single distinct pair x,y and a basis vector u, put s = 1 − λ and gᵢ = uᵢ/√dᵢ. "
                + "The summand is s(gₓ² + gᵧ²) − 2gₓgᵧ. For positive degrees this equals the displayed source expression "
                + "with denominators dₓ, dᵧ and √(dₓdᵧ). The same definition covers edges and nonedges."),
            Node("claim", "Conjecture 2.20",
                AssessedProvenance.FromLiterature(Source),
                "Conjecture 2.20 states that over all graphs the maximum edge derivative for any pair of vertices is 1. "
                + "The universal clause ranges over every finite connected simple unweighted graph of order at least two, "
                + "every distinct pair, and every real normalized Laplacian eigenvalue of positive multiplicity. "
                + "The basis has type OrthonormalBasis on the full eigenspace, so k is its dimension. "
                + "For each such basis, the source formula is the derivative of the normalized compressed trace at zero, "
                + "is basis-independent and is at most 1. The attaining graph is the connected path on three vertices, "
                + "with the nonedge joining its endpoints and the one-dimensional eigenspace at eigenvalue 1."),
            Describe.Lean(DescribeId.Create("albright-max-edge-derivative-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The attained maximum is one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The perturbation adds t to the two opposite adjacency entries. The degree row sums "
                        + "increase by t at each endpoint. Write P = D⁻¹ᐟ² and B = PAP at zero. Differentiating each "
                        + "reciprocal square root gives L′ = (HB + BH)/2 − PCP, where C is the perturbation matrix "
                        + "and H has diagonal dᵢ′/dᵢ. On an s-eigenvector of B, the resulting quadratic form is "
                        + "the Lemma 2.3 summand. The trace identity and derivative uniqueness give independence of basis.")),
                    Paragraph(Text("The ordinary graph Laplacian and the sum of squares over ordered adjacent pairs give "
                        + "the inequalities for I − B and I + B. Thus −1 ≤ s ≤ 1. Completing a square bounds the "
                        + "summand by (1 + s)(gₓ² + gᵧ²). If s ≤ 0, degrees are at least one and the endpoint mass "
                        + "is at most one. For s > 0 and adjacent endpoints with degrees at least two, the scaled "
                        + "endpoint mass is at most one half. At a leaf on an adjacent pair, the eigenvector "
                        + "equation gives gᵧ = s gₓ after labelling the leaf x, and the summand is nonpositive.")),
                    Paragraph(Text("For a nonedge let w be u restricted to x and y, and let m = uₓ² + uᵧ². "
                        + "Then wᵀBw = 0 and wᵀu = wᵀw = m. Evaluating the quadratic form of I + B on w − mu "
                        + "gives m − (1 + s)m² ≥ 0. With m > 0 this yields (1 + s)m ≤ 1. The case m = 0 gives "
                        + "a zero summand. Every basis vector therefore contributes at most one, so the average "
                        + "has the same bound for every positive multiplicity.")),
                    Paragraph(Text("For the path on three vertices, the unit vector (1,0,−1)/√2 spans the "
                        + "eigenspace at 1. The perturbed normalized Laplacian on this vector has eigenvalue "
                        + "1 + t/(1 + t) near zero. Its derivative at zero is 1."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("albright-et-al-2023-max-edge-derivative-conjecture-2-20"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, AssessedProvenance provenance,
        string prose) => Describe.Lean(DescribeId.Create("albright-max-edge-derivative-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
