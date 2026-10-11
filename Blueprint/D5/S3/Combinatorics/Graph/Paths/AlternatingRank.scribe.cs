using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Paths;

internal sealed class AlternatingRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Paths/AlternatingRank.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The alternating sum of binary adjacency ranks over the edge subsets of every nonempty path is minus two. A single colour word then separates each proper partition from all partitions that do not refine it, proving independence of the two- and three-block partition rank functions.",
        H("Path rank differences and partition independence"),
        Blocks(
            Node("adjacency", "Edge-subgraph adjacency", AdjacencyFormula(),
                "For n natural and w:Fin(n)→Bool, adjacency(w) is a matrix over ZMod 2 on n+1 distinct vertices. Its entries at (i,i+1) and (i+1,i) equal one precisely when w(i)=true; all other entries are zero. In the display, e_w(i,j) means that there is k:Fin(n) with w(k)=true and either (i,j)=(k,k+1) or (i,j)=(k+1,k). The definition recursively splits off the first row and column. Repeated colours in a later colouring never identify physical vertices.", DescribeRole.Definition),
            Node("alternatingRank", "Alternating rank sum", AlternatingFormula(),
                "The sum is over every Boolean edge word, including the empty word. E(w) is the set of indices on which w is true. Ranks are natural numbers cast to the integers, and every sign and sum is computed in the integers. The empty path has one vertex and rank zero.", DescribeRole.Definition),
            Node("alternating_rank", "Nonempty paths have alternating rank minus two", RankFormula(),
                "For every positive n the alternating rank is -2. If the first edge is absent, deleting its isolated endpoint leaves the rank unchanged. If it is present, the first kernel equation sets the next vertex coordinate to zero, the second determines the first coordinate, and the remaining kernel is exactly that of the path with the first two vertices removed. Rank-nullity therefore increases the rank by two. Pairing the choices of the second edge cancels this branch of the signed sum, leaving the same sum for a path one edge shorter. A single edge has rank two when retained and rank zero when absent. This proves the identity without assuming a matching-number formula.", DescribeRole.Theorem),
            Node("maskedAdjacency", "Partition masking", MaskFormula(),
                "For every colour type, vertex count N, equivalence relation sigma on colours, colouring c:Fin(N)→alpha, and binary matrix A, maskedAdjacency deletes precisely the entries whose endpoint colours are equivalent under sigma. No surjectivity is required of c. Setoid.ker(P.part) is the equivalence relation of belonging to the same block of a finite partition P.", DescribeRole.Definition),
            Node("path_separator", "One path separates all test partitions", SeparatorFormula(),
                "For every finite colour type and proper equivalence relation pi, there exist a positive path length n and one colour word c:Fin(n+1)→alpha such that the displayed equation holds for every equivalence relation sigma. Here L(n,c,sigma) is the sum over all Boolean edge words w of (-1)^|E(w)| times rank_F2(maskedAdjacency(sigma,c,adjacency(w))). The order sigma≤pi is refinement: sigma(x,y) implies pi(x,y). A walk in the complete multipartite colour graph visits every cross-block colour pair; placing its successive colours on distinct vertices gives the path. If sigma merges one of those pairs, toggling its edge occurrence preserves the masked matrix and reverses the integer sign. Otherwise every edge is preserved and the preceding path identity applies. With complementary-edge signs (-1)^(n-|E(w)|), the nonzero value is instead 2(-1)^(n-1).", DescribeRole.Theorem),
            Node("partition_rank_independent", "Independence for every number of parties", IndependenceFormula(),
                "For every natural q≥2, I(q) consists of all finite partitions of Fin(q) having exactly two or three nonempty blocks. Let a:I(q)→R. If the weighted rank sum vanishes for every natural N, every symmetric zero-diagonal matrix A over ZMod 2 on Fin(N), and every colouring c:Fin(N)→Fin(q), then every coefficient is zero. The displayed r(P,c,A) is the real cast of rank(maskedAdjacency(Setoid.ker(P.part),c,A)); the displayed hypothesis quantifies all matrices and colourings as above. Applying each single-path separator to the common linear relation gives the sum of coefficients over every refinement ideal. A minimal nonzero coefficient contradicts that equation. The argument allows empty colour classes and N=0. It proves the graph-rank statement; a conclusion about normalized stabilizer states or entropy weights additionally requires a graph-state realization and the relevant entropy identity.", DescribeRole.Theorem),
            Paragraph(Text("The rank-nullity theorem, finite-sum rearrangement, and minimal-element argument are standard. The path difference and its partition application are presented as a derivation, without a claim of literature priority. No assertion about other replica indices, mixed states, or non-stabilizer states is made.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create("path-rank-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula All(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula SumOver(string v, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(v), Colon, domain)), body);
    private static Formula NegTwo() => new Formula.Negate(D(2));
    private static Formula Words(Formula n) => new Formula.TypeArrow(Fin(n), Name("Bool"));
    private static Formula Colours(Formula n, Formula a) => new Formula.TypeArrow(Fin(Add(n, D(1))), a);

    private static Formula AdjacencyFormula()
    {
        var n = F.Id("n"); var w = F.Id("w"); var i = F.Id("i"); var j = F.Id("j");
        var entries = Eq(Call("adjacency", w, i, j), Call("indicator", Call("e", w, i, j)));
        return Disp(All("n", Nats(), All("w", Words(n),
            All("i", Fin(Add(n, D(1))), All("j", Fin(Add(n, D(1))), entries)))));
    }

    private static Formula AlternatingFormula() => Disp(All("n", Nats(),
        Eq(Call("alternatingRank", F.Id("n")), SumOver("w", Words(F.Id("n")),
            Mul(new Formula.Power(new Formula.Negate(D(1)), Call("card", Call("E", F.Id("w")))),
                Call("rank", Call("adjacency", F.Id("w"))))))));

    private static Formula RankFormula() => Disp(All("n", Nats(), Implies(Lt(D(0), F.Id("n")),
        Eq(Call("alternatingRank", F.Id("n")), NegTwo()))));

    private static Formula MaskFormula() => Disp(Eq(Call("maskedAdjacency", F.Id("sigma"),
        F.Id("c"), F.Id("A"), F.Id("i"), F.Id("j")), Call("if", Call("sigma", Call("c", F.Id("i")),
            Call("c", F.Id("j"))), D(0), Call("A", F.Id("i"), F.Id("j")))));

    private static Formula SeparatorFormula()
    {
        var alpha = F.Id("alpha"); var pi = F.Id("pi"); var sigma = F.Id("sigma");
        var n = F.Id("n"); var c = F.Id("c");
        var separation = Eq(Call("L", n, c, sigma), Call("if", Le(sigma, pi), NegTwo(), D(0)));
        var commonWord = Ex("n", Nats(), And(Lt(D(0), n),
            Ex("c", Colours(n, alpha), All("sigma", Call("Setoid", alpha), separation))));
        return Disp(All("alpha", Name("FiniteType"),
            All("pi", Call("Setoid", alpha), Implies(Call("proper", pi), commonWord))));
    }

    private static Formula VanishingFormula()
    {
        var n = F.Id("N"); var a = F.Id("A"); var c = F.Id("c"); var p = F.Id("P");
        var sum = SumOver("P", Call("I", F.Id("q")), Mul(Call("a", p), Call("r", p, c, a)));
        return All("N", Nats(), All("A", Call("Matrix", Fin(n), Fin(n), Call("ZMod", D(2))),
            Implies(And(Call("IsSymm", a), All("j", Fin(n), Eq(Call("A", F.Id("j"), F.Id("j")), D(0)))),
                All("c", new Formula.TypeArrow(Fin(n), Fin(F.Id("q"))), Eq(sum, D(0))))));
    }

    private static Formula IndependenceFormula() => Disp(All("q", Nats(), Implies(Le(D(2), F.Id("q")),
        All("a", new Formula.TypeArrow(Call("I", F.Id("q")), Reals()),
            Implies(VanishingFormula(), All("P", Call("I", F.Id("q")),
                Eq(Call("a", F.Id("P")), D(0))))))));
}
