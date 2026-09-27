using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class DirectProductCyclePathBootstrapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/bresar2024bootstrapdirect");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In 2-neighbour bootstrap percolation on the direct product of the cycle C_n and the path P_m, the least size of a percolating set is n for every n at least 3 and m at least 1. This settles Problem 5 of Brešar, Hedžet and Herrman.",
        H("The 2-neighbour bootstrap percolation number of C_n x P_m is n"),
        Blocks(
            Node("dirprod", "The direct product of graphs", DirProdFormula(),
                "The direct product G x H has the pairs (g, h) as vertices; (g, h) and (g', h') are adjacent when g, g' are adjacent in G and h, h' are adjacent in H.",
                "dirProd", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("step", "One round of r-neighbour bootstrap percolation", StepFormula(),
                "A round keeps every infected vertex and infects every vertex with at least r infected neighbours: A_t = A_(t-1) together with the vertices v with |N(v) ∩ A_(t-1)| at least r.",
                "step", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("percolates", "Percolating sets", PercolatesFormula(),
                "A set A percolates when some number of rounds, started from A, infects every vertex.",
                "Percolates", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("number", "The bootstrap percolation number m(G, r)", NumberFormula(),
                "m(G, r) is the least size of a nonempty percolating set.",
                "percolationNumber", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Problem 5", ClaimFormula(),
                "For every n at least 3 and m at least 1, m(C_n x P_m, 2) = n, with C_n the cycle on the vertices 0, ..., n - 1 and P_m the path on the vertices 0, ..., m - 1.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof", Disp(F.Id("claim")),
                "Upper bound (Proposition 3 of the paper): the layer of the path vertex 0 percolates, since a vertex (a, b + 1) has the two distinct neighbours (a - 1, b) and (a + 1, b) in the layer b, so t rounds infect the layers 0, ..., t. Lower bound: let D(A) be the sum over v in A of |N(v) ∩ A|, twice the number of edges inside A. One round adds a set B disjoint from A in which every vertex has at least 2 neighbours in A; counting the pairs of adjacent vertices in A and B from both sides gives D(A ∪ B) at least D(A) + 4|B|, so 4|A| - D(A) never increases. On the whole vertex set of C_n x P_m the degree of (a, b) is twice the degree of b in P_m, and the degrees of P_m sum to 2(m - 1), so 4|V| - D(V) = 4nm - 4n(m - 1) = 4n. Hence a percolating set A satisfies 4n at most 4|A| - D(A), which is at most 4|A|, and |A| is at least n.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bresar-2024-direct-product-cycle-path-percolation"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("bootcp-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Adj(Formula graph, Formula a, Formula b) => Call("Adj", graph, a, b);
    private static Formula Card(Formula set) => Call("card", set);

    private static Formula DirProdFormula()
    {
        Formula g = F.Id("G"), h = F.Id("H"), x = F.Id("x"), y = F.Id("y");
        return Disp(Iff(Adj(Call("dirProd", g, h), x, y),
            And(Adj(g, Call("fst", x), Call("fst", y)), Adj(h, Call("snd", x), Call("snd", y)))));
    }

    private static Formula StepFormula()
    {
        Formula g = F.Id("G"), r = F.Id("r"), a = F.Id("A"), v = F.Id("v");
        Formula infected = Seq(OpenBrace, v, Sp, Mid, Sp,
            AtMost(r, Card(Call("inter", Call("neighborFinset", g, v), a))), CloseBrace);
        return Disp(Equal(Call("step", g, r, a), Call("union", a, infected)));
    }

    private static Formula PercolatesFormula()
    {
        Formula g = F.Id("G"), r = F.Id("r"), a = F.Id("A"), t = F.Id("t");
        return Disp(Iff(Call("Percolates", g, r, a),
            Ex("t", Naturals(), Equal(Call("iterate", Call("step", g, r), t, a), Named("univ")))));
    }

    private static Formula NumberFormula()
    {
        Formula g = F.Id("G"), r = F.Id("r"), a = F.Id("A"), k = F.Id("k");
        Formula sizes = Seq(OpenBrace, k, Sp, Mid, Sp, Ex("A", Call("Finset", F.Id("V")),
            And(Call("Nonempty", a), And(Equal(Card(a), k), Call("Percolates", g, r, a)))), CloseBrace);
        return Disp(Equal(Call("percolationNumber", g, r), Call("sInf", sizes)));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m");
        Formula graph = Call("dirProd", Call("cycleGraph", n), Call("pathGraph", m));
        return Disp(Iff(F.Id("claim"), All("n", Naturals(), All("m", Naturals(),
            Implies(AtMost(D(3), n), Implies(AtMost(D(1), m),
                Equal(Call("percolationNumber", graph, D(2)), n)))))));
    }
}
