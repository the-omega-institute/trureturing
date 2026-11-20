using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.DiscreteGravity;

internal sealed class GeometricSpineSolutionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/DiscreteGravity/GeometricSpineSolutions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/DiscreteGravity/mazhang2026treeequations");

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every regular tree T_q, q ≥ 2, carries geometric-spine solutions of the tree equations with equal "
            + "stars off the spine, nonconstant exactly when r ≠ 1, and with nonconstant curvature.",
        H("Geometric-spine solutions of the tree equations on every regular tree"),
        Blocks(
            Def("geometric-spine-vtx", "Vtx", "The vertices of T_q",
                "Spine vertices n ∈ ℤ, and branch vertices (n, b, w): a word w over q letters in the "
                + "branch b ∈ {0, …, q − 2} attached at the spine vertex n."),
            Def("geometric-spine-parent", "parent", "The parent map",
                "n ↦ n − 1 on the spine; (n, b, []) ↦ n; (n, b, c :: w) ↦ (n, b, w)."),
            Def("geometric-spine-graph", "graph", "The tree T_q",
                "Each vertex is joined to its parent."),
            Def("geometric-spine-scale", "scale", "The scales", "s_n = t rⁿ."),
            Def("geometric-spine-lengths", "lengths", "The geometric-spine lengths",
                "The spine edge between n and n + 1 has length a s_n with a = (r² + 1)/(r + 1); every "
                + "branch edge at n, including the attachment edge, has length s_n."),
            Def("geometric-spine-curvature", "curvature", "Tree curvature",
                "K_ij = (2/ℓ_ij²)(1/d_i + 1/d_j) − (R_i + R_j)/ℓ_ij, equation (4.10) of Huang, Stoica, "
                + "Xia and Zhong."),
            Describe.Lean(DescribeId.Create("geometric-spine-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Geometric-spine solutions, equal stars and curvature"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every integer q ≥ 2, t > 0 and r > 0, the graph is a tree in which every "
                        + "vertex has degree q + 1. The lengths are symmetric and positive, and every "
                        + "edge satisfies (R_i² + R_j²)/ℓ_ij − R_i − R_j = 0, where c_i, d_i are the sums "
                        + "of 1/ℓ and 1/ℓ² over incident edges and R_i = c_i/d_i. The spine edge from n to "
                        + "n + 1 has length a s_n and R = s_n at n; at every branch vertex of the branches "
                        + "at n, R = s_n and every incident length is s_n. The lengths are constant "
                        + "exactly when r = 1. Inside a branch the curvature is 4/(q + 1) − 2; on an "
                        + "attachment edge it is 2/B + 2/(q + 1) − 2 with B = q − 1 + (r + 1)²/(r² + 1), and "
                        + "the attachment value is larger exactly when r ≠ 1. For q = r = 2 these are −2/3 "
                        + "and −13/21.")),
                    Paragraph(Text(
                        "The rank n on the spine and n + 1 + |w| on branches drops by one along the parent "
                        + "map. Hence a vertex is never its own parent and every cycle has a vertex of "
                        + "maximal rank whose two cycle neighbours are both its parent, which is "
                        + "impossible; following parents reaches the spine, so the graph is a tree. At "
                        + "a spine vertex the incident lengths are a s_n / r, a s_n and q − 1 copies of "
                        + "s_n, so c = (1/s_n)((r + 1)/a + q − 1) and d = (1/s_n²)((r² + 1)/a² + q − 1); "
                        + "the two factors agree because a(r + 1) = r² + 1, giving R = s_n. Branch "
                        + "vertices have all lengths s_n. The residual vanishes on branch edges trivially "
                        + "and on spine edges because (1 + r²)/a = 1 + r. Two consecutive spine edges "
                        + "differ unless r = 1, and for r = 1 all lengths equal t. Since every branch "
                        + "vertex has equal incident lengths, Conjecture 3 of Huang, Stoica, Xia and Zhong "
                        + "fails on every T_q, q ≥ 2, and Conjecture 4 fails on T_2. The curvature "
                        + "comparison reduces to (r + 1)²/(r² + 1) < 2, that is (r − 1)² > 0. This is "
                        + "Theorem 1 and Corollaries 2 and 6 of H. Ma and W. Zhang "
                        + "(DOI 10.5281/zenodo.23935004); the equations are those of A. Huang, B. Stoica, "
                        + "X. Xia and X. Zhong (arXiv:2006.06716v1)."))),
                DescribeRole.Theorem))));
}
