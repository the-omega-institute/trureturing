using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.TokenGraph;

internal sealed class NewLayerMaximaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/reyes2023tokenspectra");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the actual connected star on four vertices, the first two new Laplacian layers have maxima 4 and 3. Their decrease refutes the whole successive-layer monotonicity conjecture.",
        H("New Laplacian layer maxima decrease on the four-vertex star"),
        Blocks(
            Node("spectrum", "The complete ordinary Laplacian spectral multiset",
                Eq(Call("spectrum", F.Id("G")), Call("map", Call("eigenvalues", Call("lapMatrix", F.Id("G"), R)), Call("univ", F.Id("V")))),
                "For any finite vertex type V with decidable equality and finite simple graph G with decidable adjacency, spectrum maps every eigenvalue index to the real eigenvalue of the Hermitian degree-minus-adjacency matrix. It retains every algebraic multiplicity. Matrix.IsHermitian.roots_charpoly_eq_eigenvalues identifies exactly this multiset with the roots of the characteristic polynomial; this identity is applied in spectrum_from_basis. It is neither the set-valued spectrum nor an adjacency spectrum.",
                "spectrum", AssessedProvenance.FromLiterature(Source)),
            Node("layer", "Consecutive multiset subtraction",
                Eq(Call("layer", F.Id("G"), F.Id("k")), Seq(Call("spectrum", Call("tokenGraph", F.Id("G"), F.Id("k"))), Sp, Minus, Sp, Call("spectrum", Call("tokenGraph", F.Id("G"), Seq(F.Id("k"), Minus, D(1)))))),
                "The existing tokenGraph uses Set.powersetCard, not a preassigned graph or matrix: its vertices are all k-element finite subsets, and its two directed singleton differences form an edge of G. For equal-size subsets these singleton differences are equivalent to the source symmetric-difference condition. Multiset subtraction removes the previous multiplicity of each eigenvalue. F_0 is the one empty subset, so its Laplacian has spectrum {0}. Only after this subtraction does rho convert to a finite set to take a maximum.",
                "layer", AssessedProvenance.FromLiterature(Source)),
            Node("rho", "The maximum on the full nonempty source domain",
                Eq(Call("rho", F.Id("G"), F.Id("k")), Call("maxPrime", Call("toFinset", Call("layer", F.Id("G"), F.Id("k"))))),
                "Definition 3.1: for 1 ≤ k ≤ floor(n/2), rho is the maximum eigenvalue in the consecutive spectral multiset difference. The Lean arguments hk and hkn prove these bounds. The consumed helper layer_nonempty proves nonemptiness for every n and every graph in this range: the two complete spectral multisets have cardinalities choose(n,k) and choose(n,k−1); the binomial recurrence and k ≤ n/2 give a strict increase. A zero multiset difference would imply the opposite cardinal inequality. Thus no nonemptiness assumption or default numeric value replaces any source case.",
                "rho", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The entire original Conjecture 3.3", ClaimFormula(),
                "Conjecture 3.3 states: For any graph G, ρ₁(G) ≤ ρ₂(G) ≤ ⋯ ≤ ρ⌊n/2⌋(G). The formal claim quantifies every n, every simple unweighted undirected graph on Fin n with decidable adjacency, and every 1 ≤ k < n/2, where division is natural-number division. Fin n provides all finite labelled graphs of every order. The bounds supplied to rho at k and k+1 are proved from this range. There is no graph-order cap, fixed-graph restriction, spectral-containment premise, replacement by full radii, or conclusion assumed as a hypothesis. The source's introductory connected-graph convention is also met by the counterexample: connectedStar stores the actual star with Mathlib's connected_starGraph proof.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("newlayer-result"),
                DeclarationHandle.Create(Prefix + "result"), H("A connected exact counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take K₁,₃ on Fin 4 with center 0. The equivalences e0, e1, e2 enumerate all actual token subsets, with e2 in the order 01,12,02,23,03,13. Decidable integer Laplacian identities verify every degree and adjacency entry. In particular the two-token matrix is the ordinary C₆ Laplacian, with two neighbors at every vertex and no extra edges. Entrywise casting preserves these actual matrices over the reals. The displayed rational matrices P and Q in spectrum1 and spectrum2 satisfy QP=I and LP=P diag(d), so their columns form complete eigenbases, not merely lists of eigenvectors. Mathlib's characteristic-polynomial identities and Hermitian roots theorem then prove the entire spectral multisets: Sp₀={0}, Sp₁={0,1,1,4}, Sp₂={0,1,1,3,3,4}. Exact multiset subtraction gives Δ₁={1,1,4} and Δ₂={3,3}; Finset.max' gives ρ₁=4 and ρ₂=3. At n=4,k=1 the original universal claim requires 4≤3, a contradiction.")),
                    Paragraph(Text("The star and six-cycle spectral ingredients occur in Dongsheng Wei, arXiv:2609.26802v1 Section 4.6 and v2 Section 7, as recorded in the source note. This calculation applies those ingredients to the consecutive new-layer multisets. Full Laplacian maxima remain 4 at both positive levels, whereas the new-layer maxima decrease. Conjecture 3.2 about minima and the separate full-radius equality characterization concern different statements."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("reyes-dalfo-fiol-2024-new-laplacian-layer-maxima"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("newlayer-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(a, op, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(name), Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), k = F.Id("k");
        Formula bounds = Logic(Le(D(1), k), FormulaLogicOperator.And, Lt(k, Call("div", n, D(2))));
        Formula comparison = Le(Call("rho", g, k), Call("rho", g, Seq(k, Plus, D(1))));
        return Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All("n", N, All("G", Call("SimpleGraph", Call("Fin", n)),
                Seq(OpenBracket, Call("DecidableRel", Call("Adj", g)), CloseBracket, Comma, Sp,
                    All("k", N, Logic(bounds, FormulaLogicOperator.Implies, comparison))))));
    }
}
