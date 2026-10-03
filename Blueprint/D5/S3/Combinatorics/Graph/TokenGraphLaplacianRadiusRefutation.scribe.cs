using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class TokenGraphLaplacianRadiusRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/song2026tokenradius");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The graph consisting of one edge and two isolated vertices has Laplacian spectral radius 2, as does its two-token graph, but it is not a star. This refutes the all-graphs statement of Conjecture 1.1 of Song, Dalfo, Fiol and Zhang.",
        H("A disconnected counterexample to the token-radius conjecture"),
        Blocks(
            Node("graph", "Moving one token", GraphFormula(),
                "The token vertices are Mathlib's Set.powersetCard V k, the finite subsets of cardinality k, with val denoting the underlying finite subset. The carrier is defined for every k; claim restricts k to the source's range. The Abstract's adjacency sentence is encoded by the two set differences. For equal-cardinality subsets, a symmetric difference equal to an edge {u,v} has one endpoint in each difference: the differences are disjoint, and equal cardinalities force their sizes to agree. Conversely, the displayed singleton differences give symmetric difference {u,v}; G.Adj u v ensures distinct endpoints. Thus this adjacency is exactly the source's adjacency. Symmetry follows by exchanging u and v, and a subset cannot be adjacent to itself.",
                "tokenGraph", AssessedProvenance.FromLiterature(Source)),
            Node("decidable", "Decidable token adjacency", DecidableFormula(),
                "On a finite carrier with decidable equality and graph adjacency, finite search over u and v decides the displayed adjacency predicate. This instance uses the existing finite-subset and subtype instances.",
                "instTokenGraphDecidableAdj", AssessedProvenance.FromRepo()),
            Node("radius", "The Laplacian spectral radius", RadiusFormula(),
                "Section 2, page 5: \"Let L = L(G) = D(G) − A(G) be the Laplacian matrix of G.\" It states: \"the spectral radius of L is ρ(L) = λ_n. We denote ρ(G) = ρ(L) as the Laplacian spectral radius of G.\" Here lapMatrix is Mathlib's degree matrix minus adjacency matrix. The indexed operator is SimpleGraph.isHermitian_lapMatrix, the canonical Hermitian proof object for this Laplacian. Its eigenvalues are real because it is Hermitian, and nonnegative because the graph Laplacian is positive semidefinite (SimpleGraph.posSemidef_lapMatrix). Therefore their maximum is also the maximum absolute eigenvalue, the source's spectral radius. supPrime denotes Finset.sup' over all eigenvalue indices, with its proof argument implicit and supplied in the nonempty branch; the empty carrier has radius zero.",
                "rho", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1.1", ClaimFormula(),
                "Section 1, page 4: \"Conjecture 1.1. Let G be a graph of order n(≥ 4), the equality ρ(F_k(G)) = ρ(G) holds for all k with 2 ≤ k ≤ ⌊n/2⌋ if and only if G ≅ S_n.\" The quantified graph is finite and simple, with vertices Fin n, labelled 0 through n−1. No connectedness hypothesis is imposed in this sentence. S_n is K_{1,n−1}, represented directly by Mathlib's starGraph centered at the Fin n vertex of value zero. Iso is Mathlib's SimpleGraph.Iso; Nonempty of this graph-isomorphism type expresses existence of an isomorphism. div means natural-number division, so div(n,2) is ⌊n/2⌋. Proof arguments establishing that vertex zero exists are implicit in the formula.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("tokrad-result"), DeclarationHandle.Create(Prefix + "result"),
                H("One edge and two isolated vertices"), StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take the graph on Fin 4 whose only edge is {0,1}. Its two-token graph has edges {0,2}–{1,2} and {0,3}–{1,3}, with {0,1} and {2,3} isolated. Both nonzero Laplacians satisfy L² = 2L. Applied to an eigenvector, this identity gives λ² = 2λ, so every eigenvalue is zero or two; if all were zero, the Hermitian matrix itself would be zero. Hence both radii are two. For n = 4, the only integer k in the conjecture's range is two. The original graph has one edge, while the star on four vertices has three; isomorphisms preserve this edge count. Thus the left side of the asserted equivalence holds and its right side fails. This result addresses the literal all-graphs statement; the version restricted to connected graphs remains open."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("tokrad-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(variable), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Graph(Formula v) => Call("SimpleGraph", v);
    private static Formula Adj(Formula g) => Call("Adj", g);
    private static Formula Tokens(Formula v, Formula k) => new Formula.Apply(Seq(F.Id("Set"), Dot, F.Id("powersetCard")), [v, k]);
    private static Formula TokenGraph(Formula g, Formula k) => Call("tokenGraph", g, k);
    private static Formula Singleton(Formula v) => Seq(OpenBrace, v, CloseBrace);
    private static Formula Difference(Formula s, Formula t) => Seq(Call("val", s), Sp, Setminus, Sp, Call("val", t));
    private static Formula FiniteGraphBinders(Formula body) =>
        All("V", F.Id("Type"), Instance(Call("Fintype", F.Id("V")),
            Instance(Call("DecidableEq", F.Id("V")), All("G", Graph(F.Id("V")),
                Instance(Call("DecidableRel", Adj(F.Id("G"))), body)))));

    private static Formula GraphFormula()
    {
        Formula v = F.Id("V"), k = F.Id("k"), s = F.Id("s"), t = F.Id("t");
        Formula u = F.Id("u"), w = F.Id("v");
        Formula predicate = Logic(Equal(Difference(s, t), Singleton(u)), FormulaLogicOperator.And,
            Logic(Equal(Difference(t, s), Singleton(w)), FormulaLogicOperator.And,
                Call("Adj", F.Id("G"), u, w)));
        Formula exists = Seq(Exists, Sp, Parenthesized(Seq(u, Sp, Colon, Sp, v)), Sp,
            Parenthesized(Seq(w, Sp, Colon, Sp, v)), Comma, Sp, predicate);
        Formula body = Logic(Call("Adj", TokenGraph(F.Id("G"), k), s, t), FormulaLogicOperator.Iff, exists);
        return Disp(All("V", F.Id("Type"), Instance(Call("DecidableEq", v),
            All("G", Graph(v), All("k", Naturals(),
                All("s", Tokens(v, k), All("t", Tokens(v, k), body)))))));
    }

    private static Formula DecidableFormula() => Disp(FiniteGraphBinders(
        All("k", Naturals(), Call("DecidableRel", Adj(TokenGraph(F.Id("G"), F.Id("k")))))));

    private static Formula RadiusFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G");
        Formula indices = Call("univ", v);
        Formula rr = Seq(Mathbb, Grp(F.Id("R")));
        Formula proof = new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id("isHermitian"), Underscore, Grp(F.Id("lapMatrix"))))), [rr, g]);
        Formula eigenvalues = Call("eigenvalues", proof);
        Formula rhs = Seq(Left, OpenBrace, new Formula.Aligned([Seq(Call("supPrime", indices, eigenvalues), Sp, Amp, Sp, F.Text, Grp(F.Id("if")), Sp, Call("Nonempty", indices)), Seq(D(0), Sp, Amp, Sp, F.Text, Grp(F.Id("otherwise")))]), Right, Dot);
        return Disp(FiniteGraphBinders(Equal(Call("rho", g), rhs)));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), k = F.Id("k");
        Formula equality = Equal(Call("rho", TokenGraph(g, k)), Call("rho", g));
        Formula allK = All("k", Naturals(), Logic(Le(D(2), k), FormulaLogicOperator.Implies,
            Logic(Le(k, Call("div", n, D(2))), FormulaLogicOperator.Implies, equality)));
        Formula star = Call("starGraph", Seq(Langle, D(0), Rangle, Sp, Colon, Sp, Fin(n)));
        Formula iso = Call("Nonempty", Call("Iso", g, star));
        Formula graphs = All("G", Graph(Fin(n)), Instance(Call("DecidableRel", Adj(g)),
            Logic(allK, FormulaLogicOperator.Iff, iso)));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All("n", Naturals(), Logic(Le(D(4), n), FormulaLogicOperator.Implies, graphs))));
    }
}
