using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class JeanSeoCubicErrorDetectingCodeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/JeanSeoCubicErrorDetectingCode.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/jeanseo2022errordetection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected cubic graph on fifty vertices has an error-detecting identifying code with thirty-six detectors.",
        H("A cubic error-detecting identifying code below density three quarters"),
        Blocks(
            Node("closedDominators", "Closed detector neighborhoods", DescribeRole.Definition,
                ClosedDominatorsBody(), AssessedProvenance.FromLiterature(Source),
                "Page 1, Section 1: \"The closed neighborhood of a vertex v ∈ V(G), denoted N[v], is N(v) ∪ {v}.\" The same paragraph states \"N_S[u] = N[u] ∩ S\". Here V is the vertex type, G is a finite simple graph, S is its detector set, and u is a vertex. Finset union with the singleton includes u itself; intersection retains exactly the detectors."),
            Node("IsDETIC", "Error-detecting identifying codes", DescribeRole.Definition,
                IsDETICBody(), AssessedProvenance.FromLiterature(Source),
                "Page 3, Theorem 2.1: \"A detector set, S ⊆ V(G), is a DET:IC if and only if each vertex is at least 2-dominated and all pairs are 2#-distinguished.\" Page 2, Definition 3: \"If S is a dominating set and u, v ∈ V(G), u and v are k#-distinguished if |N_S[u] − N_S[v]| ≥ k or |N_S[v] − N_S[u]| ≥ k.\" The first conjunct requires two closed dominators at every vertex; the second tests both directed differences for each distinct pair, with k=2."),
            Node("claim", "The cubic density conjecture", DescribeRole.Definition,
                Equal(Q("claim"), Parenthesized(ClaimBody())), AssessedProvenance.FromLiterature(Source),
                "Page 9, Section 4.2.2: \"Conjecture 1. For a cubic graph G, DET:IC%(G) ≥ 3/4.\" Page 3 states \"Note that density is also defined for finite graphs.\" The finite assertion says that every error-detecting identifying code has cardinality divided by graph order at least three quarters. Graphs are simple and cubic means degree three at every vertex. Connectedness restricts the domain; a connected counterexample also disproves the assertion without that restriction. All displayed quotients are rational."),
            Node("result", "The conjectured lower bound fails", DescribeRole.Theorem,
                new Formula.Not(Parenthesized(ClaimBody())), AssessedProvenance.FromRepo(Source),
                "The vertices 0 through 49 form a connected cubic graph. Vertices 14 through 49 are detectors, giving cardinality 36 and density 36/50=18/25<3/4. The eight A and six B vertices are outside the code; the twelve vertices of each of the P, Q and R types belong to it. Their closed detector neighborhoods have sizes 3, 2, 2, 4 and 3 respectively. Explicit finite neighborhood tables verify two-domination and directed separation, and a spanning tree verifies connectedness. This finite counterexample disproves the lower bound; it asserts neither minimality of this code nor optimality of 18/25 over cubic graphs. The source's examples at densities 3/4 and 7/8 remain compatible with this counterexample."))));

    private static DocumentBlock Node(string selector, string title, DescribeRole role,
        Formula formula, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("jeanseo-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ClosedDominatorsBody()
    {
        var v = X("V"); var g = X("G"); var s = X("S"); var u = X("u");
        return GraphBinders(true, All("S", Call("Finset", v), All("u", v,
            Equal(Call("closedDominators", g, s, u),
                Call("Inter.inter", Parenthesized(Seq(Call("SimpleGraph.neighborFinset", g, u), Cup,
                    new Formula.SetLiteral([u]))), s)))));
    }

    private static Formula IsDETICBody()
    {
        var v = X("V"); var g = X("G"); var s = X("S");
        Formula Neighborhood(Formula x) => Call("closedDominators", g, s, x);
        Formula Difference(Formula a, Formula b) =>
            Call("Finset.card", Parenthesized(Seq(Neighborhood(a), Setminus, Neighborhood(b))));
        var dominates = All("v", v, Leq(D(2), Call("Finset.card", Neighborhood(X("v")))));
        var separates = All("u", v, All("v", v, Imp(Ne(X("u"), X("v")),
            Or(Leq(D(2), Difference(X("u"), X("v"))),
                Leq(D(2), Difference(X("v"), X("u")))))));
        return GraphBinders(true, All("S", Call("Finset", v),
            Equal(Call("IsDETIC", g, s), Parenthesized(And(dominates, separates)))));
    }

    private static Formula ClaimBody()
    {
        var v = X("V"); var g = X("G"); var s = X("S");
        var bound = Leq(new Formula.Fraction(Cast(D(3), Rational()), D(4)),
            new Formula.Fraction(Cast(Call("Finset.card", s), Rational()),
                Cast(Call("Fintype.card", v), Rational())));
        return GraphBinders(false, Imp(Call("SimpleGraph.IsRegularOfDegree", g, D(3)),
            Imp(Call("SimpleGraph.Connected", g), All("S", Call("Finset", v),
                Imp(Call("IsDETIC", g, s), bound)))));
    }

    private static Formula GraphBinders(bool polymorphic, Formula body) =>
        All("V", polymorphic ? Seq(X("Type"), Star) : X("Type"),
            Seq(OpenBracket, Call("Fintype", X("V")), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", X("V")), CloseBracket, Comma, Sp,
                All("G", Call("SimpleGraph", X("V")),
                    Seq(OpenBracket, Call("DecidableRel", Q("G.Adj")), CloseBracket, Comma, Sp, body))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string name)
    {
        var parts = name.Split('.');
        var tokens = new List<Formula>();
        foreach (var part in parts)
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Q(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Rational() => Seq(Mathbb, Grp(X("Q")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
}
