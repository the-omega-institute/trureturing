using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CliquePolynomial;

internal sealed class TeimooriFaalFlatCliqueRootsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/teimoorifaal2021flat");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four complete four-vertex graphs joined in a ring give a twelve-vertex counterexample to Conjecture 1 of On Clique Roots of Flat Graphs.",
        H("A flat graph whose clique polynomial has a nonreal root"),
        Blocks(
            Node("polynomial", "The clique polynomial", "cliquePoly", PolynomialFormula(),
                "Page 1: \"For a given graph G, a complete subgraph of G with i-vertices (i ≥ 1) is called an i-clique of G.\" Equation (1) defines C(G, x) = ∑_{k=0}^{ω(G)} c_k(G)x^k, \"where by convention c₀(G) is taken to be 1 for any simple graph G.\" Here c_k(G) counts Mathlib's SimpleGraph.cliqueFinset k. The Lean sum includes the empty clique and all sizes from 0 through Fintype.card V; terms beyond the clique number are zero. Coefficients are integers; Polynomial.C embeds each count as a constant polynomial, and Polynomial.X is the polynomial variable.",
                AssessedProvenance.FromLiterature(Source)),
            Node("flat", "Flatness", "IsFlat", FlatFormula(),
                "Definition 2.2, page 4: \"A graph G is called flat if every edge of G belongs to at most two triangles of G.\" For an edge uv, the third vertex of each triangle is a common neighbour of u and v. The filtered finite set counts these third vertices.",
                AssessedProvenance.FromLiterature(Source)),
            Node("triangles", "Absence of isolated triangles", "NoIsolatedTriangle", TriangleFormula(),
                "Definition 4.1, page 6: \"For a triangle δ = {u, v, w} ⊂ V(G), the value of δ in G denoted by val_G(δ) is defined by val_G(δ) = N_G(u) ∩ N_G(v) ∩ N_G(w). Moreover, a triangle is called isolated if its triangle value is zero.\" Thus every triangle must have a vertex adjacent to all three of its vertices. Adjacency is irreflexive, so this common neighbour differs from each triangle vertex.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Teimoori Faal's Conjecture 1", "claim", Iff(F.Id("claim"), Parenthesized(ClaimBody())),
                "Conjecture 1, page 6: \"The class of 2-connected K₅-free flat graphs without isolated triangles has only clique roots. In particular, this class has always the clique root r = −1 of multiplicity 2.\" The source, page 4, says \"we will call a real root of C(G, x) a clique root of G.\" Accordingly, all complex zeros must have imaginary part zero. The second conjunct says that −1 has root multiplicity exactly two. The vertex type is finite, adjacency is decidable, and there are at least three vertices. Biconnected means connected and connected after deletion of any one vertex; it is the existing D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.Biconnected predicate. K₅-freeness is SimpleGraph.CliqueFree 5.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("tf-flat-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A twelve-vertex refutation"), StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take the four complete blocks {0,1,4,5}, {1,2,6,7}, {2,3,8,9}, and {3,0,10,11}, with no other edges. A Hamiltonian cycle remains a spanning path after deleting any vertex. Finite clique enumeration verifies K₅-freeness, flatness and the absence of isolated triangles, and gives the clique counts 1,12,24,16,4, followed by zeros. Hence the clique polynomial is p = 1+12X+24X²+16X³+4X⁴ = 4(1+X)⁴−4X−3. Its derivative is 16(1+X)³−4, with at most one real root and no repeated real roots. The root-count inequality for a polynomial and its derivative precludes splitting of p over ℝ. Splitting over ℂ then supplies a nonreal complex zero, contradicting the first conjunct of the conjecture."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("teimoori-faal-2021-flat-graph-clique-roots-conjecture-1"),
                    ResolutionKind.Refuted))), []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("tf-flat-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula Qualified(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(Qualified(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instances(Formula body, params Formula[] types)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var type in types) items.Add(Seq(OpenBracket, type, CloseBracket, Sp));
        items.Add(body);
        return Seq([.. items]);
    }
    private static Formula Relation(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Vertex() => F.Id("V");
    private static Formula Graph() => Call("SimpleGraph", Vertex());
    private static Formula Adj(Formula u, Formula v) => Call("SimpleGraph.Adj", F.Id("G"), u, v);
    private static Formula GraphBinders(Formula body, bool decidableEquality) => All("V", F.Id("Type"),
        Instances(All("G", Graph(), Instances(body, Call("DecidableRel", Qualified("G.Adj")))),
            decidableEquality ? [Call("Fintype", Vertex()), Call("DecidableEq", Vertex())] : [Call("Fintype", Vertex())]));

    private static Formula PolynomialFormula()
    {
        Formula j = F.Id("j"), g = F.Id("G");
        Formula size = new Formula.Binary(Call("Fintype.card", Vertex()), FormulaBinaryOperator.Add, D(1));
        Formula range = Call("Finset.range", Parenthesized(size));
        Formula count = Parenthesized(Seq(Call("Finset.card", Call("SimpleGraph.cliqueFinset", g, j)), Sp, Colon, Sp, Integers()));
        Formula summand = new Formula.Binary(Call("Polynomial.C", count), FormulaBinaryOperator.Multiply,
            new Formula.Power(Call("Polynomial.X"), j));
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(j, Sp, InMacro, Sp, range)), Sp, summand);
        return GraphBinders(Equal(Call("cliquePoly", g), sum), true);
    }
    private static Formula FlatFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v"), w = F.Id("w");
        Formula filter = Call("Finset.filter", Parenthesized(Seq(LambdaLower, Sp, w, Sp,
            Mapsto, Sp, Parenthesized(And(Adj(u, w), Adj(v, w))))), Call("Finset.univ"));
        Formula body = All("u", Vertex(), All("v", Vertex(), Imp(Adj(u, v), AtMost(Call("Finset.card", filter), D(2)))));
        return GraphBinders(Iff(Call("IsFlat", F.Id("G")), Parenthesized(body)), false);
    }
    private static Formula TriangleFormula()
    {
        Formula u = F.Id("u"), v = F.Id("v"), w = F.Id("w"), x = F.Id("x");
        Formula body = All("u", Vertex(), All("v", Vertex(), All("w", Vertex(),
            Imp(Adj(u, v), Imp(Adj(v, w), Imp(Adj(u, w),
                Some("x", Vertex(), And(Adj(u, x), And(Adj(v, x), Adj(w, x))))))))));
        return All("V", F.Id("Type"), All("G", Graph(), Iff(Call("NoIsolatedTriangle", F.Id("G")), Parenthesized(body))));
    }
    private static Formula ClaimBody()
    {
        Formula g = F.Id("G"), z = F.Id("z"), polynomial = Call("cliquePoly", g);
        Formula allRoots = All("z", Complexes(), Imp(Equal(Call("Polynomial.aeval", z, polynomial), D(0)), Equal(Call("Complex.im", z), D(0))));
        Formula multiplicity = Equal(Call("Polynomial.rootMultiplicity", Parenthesized(new Formula.Negate(D(1))), polynomial), D(2));
        Formula conclusion = And(allRoots, multiplicity);
        Formula body = Imp(AtMost(D(3), Call("Fintype.card", Vertex())),
            Imp(Call("D5.S3.StatisticalMechanics.DimerVirialFourthDifferenceRefutation.Biconnected", g),
                Imp(Call("SimpleGraph.CliqueFree", g, D(5)),
                    Imp(Call("IsFlat", g), Imp(Call("NoIsolatedTriangle", g), conclusion)))));
        return GraphBinders(body, true);
    }
}
