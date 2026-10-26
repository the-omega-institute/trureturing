using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.TokenGraph;

internal sealed class CutBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/apteparekhsud2025tokenbounds");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A phase product on the 100-token graph of the five-cycle blow-up with block size 40 has Rayleigh quotient below the cut and matching bound of Apte, Parekh and Sud.",
        H("The token-graph cut bound fails on a five-cycle blow-up"),
        Blocks(
            Node("crosses", "An unordered edge crossing a cut", CrossesFormula(),
                "Page 8: \"Let δ(S) be the set of edges in G that cross from S to V ∖ S, and Cut(S) be the sum of the weights of the edges δ(S).\" Exactly one endpoint belongs to S. Sym2.lift descends the displayed symmetric endpoint predicate to unordered pairs; its proof of symmetry is implicit.",
                "crosses", AssessedProvenance.FromLiterature(Source)),
            Node("cut", "The maximum cut", CutFormula(),
                "Page 8: \"We denote the maximum of Cut(S) over all S by C(G), i.e., C(G) is the solution to the Maximum Cut (MaxCut) problem on G.\" Every edge has weight one, so the weight of a cut is the cardinality of the filtered unordered edge set. Finset.sup over all finite subsets gives the maximum, including the empty cut.",
                "maxCut", AssessedProvenance.FromLiterature(Source)),
            Node("matching", "The size-restricted maximum matching", MatchingFormula(),
                "Page 8: \"Let M_k(G) denote the maximum weight matching under the restriction that |M| ≤ k.\" For unit weights, weight is cardinality. The powerset ranges over edge subsets; Pairwise requires disjoint endpoint sets for distinct edges, and the cardinality is at most k. The coercion from an unordered edge to its endpoint set and that from a finite edge family to a set are shown explicitly.",
                "maxMatchingLe", AssessedProvenance.FromLiterature(Source)),
            Node("minimum", "The least real adjacency eigenvalue", MinimumFormula(),
                "Page 9: \"Let λ_max(·), λ_min(·), and eigs(·) describe the maximum eigenvalue, minimum eigenvalue, and the set of unique eigenvalues of a matrix.\" The adjacency matrix is real and Hermitian. The nonempty branch uses Finset.inf' on Matrix.IsHermitian.eigenvalues, the real eigenvalues with multiplicity. Its dependent proof arguments hA and h appear explicitly. The empty-carrier and non-Hermitian extensions are zero; neither extension is used in the counterexample.",
                "lambdaMin", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 7", ClaimFormula(),
                "Appendix D.2, page 39: \"In contrast, the following bound was shown to hold on our dataset\"; \"Conjecture 7. For all G and for all 1 ≤ k ≤ ⌊n/2⌋\" followed by \"λ_min(A(F_k(G))) ≥ −(C(G)+M_k(G))/2.\" The formula quantifies all finite simple graphs with decidable adjacency, with unit edge weights. This is a specialization of the source's all-graphs assertion. Fin n labels the n vertices; Nat.div n 2 is floor(n/2). The tokenGraph is the existing finite-subset graph: two equally sized subsets differ by one token moved along an edge. The natural cut and matching cardinalities are coerced to real numbers before division by two. No connectedness or bipartiteness hypothesis is imposed.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("apscut-adjacency-map"),
                DeclarationHandle.Create(Prefix + "adjMatrix_complex_map"),
                H("Real and complex adjacency matrices"),
                StatementSource.FromAuthor(Disp(AdjacencyMapFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Mapping the real zero-one adjacency matrix entrywise by Complex.ofReal gives the complex adjacency matrix. This identity lets lambdaMin40 apply the complex Rayleigh estimate to the real adjacency matrix."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("apscut-result"),
                DeclarationHandle.Create(Prefix + "result"), H("A phase test contradicts the bound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take the five-cycle blow-up with five independent blocks of size 40 and complete bipartite edges between successive blocks. Its 100-token graph uses the existing tokenGraph. Put z = (−4+3i)/5 and multiply z to the block index over the occupied vertices. Each phase has modulus one. Each oriented edge of the original graph occurs as a token move in choose(198,99) token subsets, so the energy reduces to a sum over the original graph. The squared norm is choose(200,100), and the ratio of these binomial coefficients is 50/199. The real part of the edge-phase sum is 2·40²·(4 Re z + Re z⁴), with 4 Re z + Re z⁴ = −2527/625. The quotient is −646912/199. Splitting the complex phase vector into its real and imaginary parts connects this quotient to the least eigenvalue of the real adjacency matrix. The cut weight is affine in each block occupancy; rounding each occupancy to zero or 40 gives at most four cut cycle edges, hence maximum cut at most 6400. The matching weight is at most 100. The conjectured lower bound is therefore at least −3250, whereas the least eigenvalue is at most −646912/199, smaller by 162/199."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("apte-parekh-sud-2025-token-graph-cut-bound"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("apscut-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Mem(Formula x, Formula s) => Seq(x, Sp, InMacro, Sp, s);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Fs(Formula v) => Call("Finset", v);
    private static Formula Un(Formula v) => Parenthesized(Seq(Q("Finset", "univ"), Colon, Sp, Fs(v)));
    private static Formula Card(Formula s) => App(Q("Finset", "card"), s);
    private static Formula GraphBinders(Formula body) => All("n", N,
        All("G", Call("SimpleGraph", Fin(F.Id("n"))),
            Instance(Call("DecidableRel", App(Q("SimpleGraph", "Adj"), F.Id("G"))), body)));

    private static Formula AdjacencyMapFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G");
        Formula c = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = App(Q("SimpleGraph", "adjMatrix"), R, g);
        Formula complex = App(Q("SimpleGraph", "adjMatrix"), c, g);
        return All("n", F.Id("Type"), Instance(Call("Fintype", n),
            Instance(Call("DecidableEq", n), All("G", Call("SimpleGraph", n),
                Instance(Call("DecidableRel", App(Q("SimpleGraph", "Adj"), g)),
                    Eq(App(Q("Matrix", "map"), real, Q("Complex", "ofReal")), complex))))));
    }

    private static Formula CrossesFormula()
    {
        Formula n = F.Id("n"), s = F.Id("S"), e = F.Id("e");
        Formula u = F.Id("u"), v = F.Id("v");
        Formula differs = new Formula.Relation(Parenthesized(Mem(u, s)),
            FormulaRelationOperator.NotEqual, Parenthesized(Mem(v, s)));
        Formula lifted = App(Q("Sym2", "lift"),
            Seq(Langle, Sp, Lambda("u", Fin(n), Lambda("v", Fin(n), differs)), Rangle), e);
        return Disp(All("n", N, All("S", Fs(Fin(n)),
            All("e", Call("Sym2", Fin(n)), Logic(Call("crosses", s, e),
                FormulaLogicOperator.Iff, lifted)))));
    }

    private static Formula CutFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), s = F.Id("S"), e = F.Id("e");
        Formula edges = App(Q("SimpleGraph", "edgeFinset"), g);
        Formula cut = App(Q("Finset", "filter"), Lambda("e", Call("Sym2", Fin(n)),
            Call("crosses", s, e)), edges);
        Formula rhs = App(Q("Finset", "sup"), Un(Fs(Fin(n))),
            Lambda("S", Fs(Fin(n)), Card(cut)));
        return Disp(GraphBinders(Eq(Call("maxCut", g), rhs)));
    }

    private static Formula MatchingFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), k = F.Id("k"), m = F.Id("M");
        Formula e = F.Id("e"), f = F.Id("f");
        Formula edgeType = Call("Sym2", Fin(n));
        Formula edgeSet = Call("Set", Fin(n));
        Formula disjoint = Call("Disjoint", Parenthesized(Seq(e, Colon, Sp, edgeSet)),
            Parenthesized(Seq(f, Colon, Sp, edgeSet)));
        Formula relation = Lambda("e", edgeType, Lambda("f", edgeType, disjoint));
        Formula pairwise = App(Q("Set", "Pairwise"),
            Parenthesized(Seq(m, Colon, Sp, Call("Set", edgeType))), relation);
        Formula predicate = Lambda("M", Fs(edgeType), Logic(Le(Card(m), k),
            FormulaLogicOperator.And, pairwise));
        Formula families = App(Q("Finset", "filter"), predicate,
            App(Q("Finset", "powerset"), App(Q("SimpleGraph", "edgeFinset"), g)));
        Formula rhs = App(Q("Finset", "sup"), families,
            Lambda("M", Fs(edgeType), Card(m)));
        return Disp(GraphBinders(All("k", N, Eq(Call("maxMatchingLe", g, k), rhs))));
    }

    private static Formula MinimumFormula()
    {
        Formula v = F.Id("iota"), a = F.Id("A"), hA = F.Id("hA"), h = F.Id("h");
        Formula nonempty = App(Q("Finset", "Nonempty"), Un(v));
        Formula eigenvalues = App(Q("Matrix", "IsHermitian"), a);
        Formula minimum = App(Seq(Q("Finset", "inf"), Apos), Un(v), h,
            Seq(hA, Dot, F.Id("eigenvalues")));
        Formula inner = Seq(F.Id("if"), Sp, h, Colon, Sp, nonempty, Sp, F.Id("then"), Sp,
            minimum, Sp, F.Id("else"), Sp, D(0));
        Formula rhs = Seq(F.Id("if"), Sp, hA, Colon, Sp, eigenvalues, Sp, F.Id("then"), Sp,
            Parenthesized(inner), Sp, F.Id("else"), Sp, D(0));
        return Disp(All("iota", F.Id("Type"), Instance(Call("Fintype", v),
            Instance(Call("DecidableEq", v), All("A", Call("Matrix", v, v, R),
                Eq(Call("lambdaMin", a), rhs))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), k = F.Id("k");
        Formula cut = Parenthesized(Seq(Call("maxCut", g), Colon, Sp, R));
        Formula matching = Parenthesized(Seq(Call("maxMatchingLe", g, k), Colon, Sp, R));
        Formula lower = new Formula.Negate(new Formula.Fraction(Add(cut, matching), D(2)));
        Formula adjacency = App(Q("SimpleGraph", "adjMatrix"), R, Call("tokenGraph", g, k));
        Formula inequality = Le(lower, Call("lambdaMin", adjacency));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, GraphBinders(All("k", N,
            Logic(Le(D(1), k), FormulaLogicOperator.Implies,
                Logic(Le(k, App(Q("Nat", "div"), n, D(2))),
                    FormulaLogicOperator.Implies, inequality))))));
    }
}
