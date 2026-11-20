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
        "Every line solution of the tree equations extends to every regular tree T_q; two-choice and "
            + "geometric spines give nonconstant solutions with equal stars off the spine and nonconstant curvature.",
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
            Def("geometric-spine-line-ratio", "lineRatio", "The line ratio",
                "For spine lengths L, with the edge from n − 1 to n of length L(n − 1), "
                + "R_n = (1/L(n − 1) + 1/L(n))/(1/L(n − 1)² + 1/L(n)²)."),
            Def("geometric-spine-line-residual", "lineResidual", "The line residual",
                "(R_n² + R_{n−1}²)/L(n − 1) − R_n − R_{n−1}, the tree equation on the line edge "
                + "from n − 1 to n."),
            Def("geometric-spine-spine-lengths", "spineLengths", "Extension of a line",
                "Spine edges keep the lengths L; every edge of the branches at n, including the "
                + "attachment edge, has length R_n."),
            Def("geometric-spine-curvature", "curvature", "Tree curvature",
                "K_ij = (2/ℓ_ij²)(1/d_i + 1/d_j) − (R_i + R_j)/ℓ_ij, equation (4.10) of Huang, Stoica, "
                + "Xia and Zhong."),
            Describe.Lean(DescribeId.Create("geometric-spine-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Geometric-spine solutions, equal stars and curvature"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every integer q ≥ 2 the graph is a tree in which every vertex has degree "
                        + "q + 1. Here c_i, d_i are the sums of 1/ℓ and 1/ℓ² over incident edges, "
                        + "R_i = c_i/d_i, and the tree equation on an edge is (R_i² + R_j²)/ℓ_ij − R_i − "
                        + "R_j = 0. For positive spine lengths L, the extension has ratio R_n at the spine "
                        + "vertex n and throughout the branches at n, every incident length at a branch "
                        + "vertex is R_n, and the extension solves the tree equations exactly when every "
                        + "line residual vanishes. For β(n) ∈ {2, 3} and L₀ > 0 there is exactly one "
                        + "sequence with L(0) = L₀ and L(n − 1) = β(n)L(n); every such sequence is "
                        + "positive, its extension solves the tree equations and is nonconstant, and the "
                        + "spine is a geometric progression exactly when β is constant. For t > 0 and "
                        + "r > 0 the geometric lengths are symmetric and positive and solve the tree "
                        + "equations; the spine edge from n to n + 1 has length a s_n and R = s_n at n; at "
                        + "every branch vertex at n, R = s_n and every incident length is s_n; the lengths "
                        + "are constant exactly when r = 1. Inside a branch the curvature is 4/(q + 1) − 2; "
                        + "on an attachment edge it is 2/B + 2/(q + 1) − 2 with B = q − 1 + (r + 1)²/(r² + 1); "
                        + "the attachment value is at least the branch value, with equality exactly when "
                        + "r = 1; and the curvature is constant on all edges exactly when r = 1.")),
                    Paragraph(Text(
                        "The rank n on the spine and n + 1 + |w| on branches drops by one along the parent "
                        + "map. Hence a vertex is never its own parent and every cycle has a vertex of "
                        + "maximal rank whose two cycle neighbours are both its parent, which is "
                        + "impossible; following parents reaches the spine, so the graph is a tree. "
                        + "Attaching m edges of length R to a vertex with c = R d gives c + m/R = R(d + m/R²), "
                        + "so ratios are preserved, branch vertices have all lengths R, branch edges have "
                        + "residual 2R²/R − 2R = 0, and spine residuals are the line residuals. For "
                        + "L(n − 1) = βL(n) the line ratio at n is L(n − 1)(β + 1)/(β² + 1), that is "
                        + "3/5 or 2/5 of L(n − 1), and the ratio at n − 1 is 6/5 of L(n − 1) for both "
                        + "choices; with u = 6/5 and v ∈ {3/5, 2/5}, u² + v² − u − v = 0. The spine "
                        + "decreases strictly, so consecutive spine edges differ. For the geometric "
                        + "spine L = a s, and at "
                        + "a spine vertex the incident lengths are a s_n / r, a s_n and q − 1 copies of "
                        + "s_n, so c = (1/s_n)((r + 1)/a + q − 1) and d = (1/s_n²)((r² + 1)/a² + q − 1); "
                        + "the two factors agree because a(r + 1) = r² + 1, giving R = s_n. Branch "
                        + "vertices have all lengths s_n. The residual vanishes on branch edges trivially "
                        + "and on spine edges because (1 + r²)/a = 1 + r. Two consecutive spine edges "
                        + "differ unless r = 1, and for r = 1 all lengths equal t. Since every branch "
                        + "vertex has equal incident lengths, Conjecture 3 of Huang, Stoica, Xia and Zhong "
                        + "fails on every T_q, q ≥ 2, and Conjecture 4 fails on T_2. The curvature "
                        + "comparison reduces to (r + 1)²/(r² + 1) < 2, that is (r − 1)² > 0, and at r = 1 all "
                        + "lengths are t and every edge has curvature 4/(q + 1) − 2. Substituting q = r = 2 "
                        + "gives B = 14/5 and the values −2/3 and −13/21. This is Theorem 1, Lemma 3 for the "
                        + "line, and Corollaries 2, 4 and 6 of H. Ma and W. Zhang "
                        + "(DOI 10.5281/zenodo.23935004); the equations are those of A. Huang, B. Stoica, "
                        + "X. Xia and X. Zhong (arXiv:2006.06716v1)."))),
                DescribeRole.Theorem))));
}
