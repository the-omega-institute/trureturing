using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class CdsoUniversalVertexRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/albalahidasalibarmanhamza2025hyperbolicsombor");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Among connected simple graphs of order seven and cyclomatic number one, every CDSO minimizer lacks a vertex adjacent to all others. A triangle with three leaves at one vertex and one leaf at a second vertex has strictly smaller CDSO than every graph with a universal vertex.",
        H("A CDSO minimizer without a universal vertex"),
        Blocks(
            Node("cdso", "The complementary diminished Sombor index", CdsoFormula(),
                "Page 109: \"We drop the factor 1/√2 from the expression (1) and call the resulting formula the complementary diminished Sombor (CDSO) index and denote it by ᶜDSO. Hence, for a graph G, we have\", followed by the sum of sqrt(d(u)²+d(v)²)/max{d(u),d(v)} over uv in E(G). SimpleGraph.degree is cast to the reals before squaring and division. SimpleGraph.edgeFinset contains each unordered edge once. Sym2.lift evaluates the symmetric function on its two endpoints; the anonymous proof stored by Lean may be replaced by any h of the displayed symmetry type, by proof irrelevance. The lambda expressions bind both endpoints with type Fin n. Every edge has two positive endpoint degrees, so its maximum degree is positive.",
                "cdso", AssessedProvenance.FromLiterature(Source)),
            Node("cyclomatic", "The literal cyclomatic number", CyclomaticFormula(),
                "Page 115: \"We recall that trees can be considered connected graphs of cyclomatic number 0, where the cyclomatic number of a graph is the minimum number of edges whose removal makes the graph acyclic.\" The set consists of the cardinalities of edge subsets whose deletion yields SimpleGraph.IsAcyclic, the absence of cyclic walks. It is nonempty because deleting all edges gives the empty graph. Its natural-number infimum is therefore its minimum. The formula explicitly coerces the finite deletion set to a set of unordered pairs. For a connected graph, extension of an acyclic subgraph to a spanning tree and the tree edge-count theorem identify this minimum through cyclomaticNumber G + n = card(edgeFinset G) + 1.",
                "cyclomaticNumber", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The CDSO half of Conjecture 4.1", ClaimFormula(),
                "Page 115, Conjecture 4.1: \"A graph minimizing (maximizing, respectively) the CDSO index (HSO index, respectively) among fixed-order connected graphs with cyclomatic number ℓ(≥ 1) has a vertex adjacent to all other vertices.\" This encoding states the CDSO half for every order n, every positive cyclomatic number ell, and every minimizer G. The comparison graph H ranges over the same connected class. Fin n labels the vertices, without restricting isomorphism types. Decidable adjacency selects finite-set representations and does not change the value of either invariant. A universal vertex v is adjacent to every w distinct from v. Refuting this half refutes the combined conjecture; the HSO half is not decided here.",
                "claim", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("cdso-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation of the universal-vertex assertion"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("On vertices 0 through 6, take the edges 01, 02, 12, 03, 04, 05 and 16. The graph is connected, has seven edges and cyclomatic number one, and its degrees are 5, 3, 2, 1, 1, 1, 1. Its CDSO is sqrt(10)/3 + sqrt(29)/5 + sqrt(34)/5 + sqrt(13)/3 + 3 sqrt(26)/5. A universal vertex in any graph of this class accounts for six edges; the unique remaining edge joins two other vertices. Relabelling thus gives the star centred at 0 with the additional edge 12, whose CDSO is sqrt(2) + 2 sqrt(10)/3 + 2 sqrt(37)/3. Rational bounds on the square roots prove a strict inequality between these two values. The finite nonempty class has a minimizer, whose value is at most the first value. Consequently every minimizer lacks a universal vertex. No assertion of uniqueness of the minimizer is needed."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("albalahi-das-ali-barman-hamza-2025-cdso-universal-vertex-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("cdso-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Seq(F.Id(owner), Dot, F.Id(name))));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Imp(Formula p, Formula q) =>
        new Formula.Logic(Parenthesized(p), FormulaLogicOperator.Implies, Parenthesized(q));
    private static Formula And(Formula p, Formula q) =>
        new Formula.Logic(Parenthesized(p), FormulaLogicOperator.And, Parenthesized(q));
    private static Formula LeqTo(Formula p, Formula q) =>
        new Formula.Relation(p, FormulaRelationOperator.LessThanOrEqual, q);
    private static Formula GraphType() => Call("SimpleGraph", Call("Fin", F.Id("n")));
    private static Formula Adj(Formula g) => Apply(Qualified("SimpleGraph", "Adj"), g);
    private static Formula Edges(Formula g) => Apply(Qualified("SimpleGraph", "edgeFinset"), g);
    private static Formula Connected(Formula g) => Apply(Qualified("SimpleGraph", "Connected"), g);
    private static Formula Index(Formula g) => Call("cdso", g);
    private static Formula Cyclomatic(Formula g) => Call("cyclomaticNumber", g);
    private static Formula Cast(Formula x, Formula t) => Parenthesized(Seq(x, Sp, Colon, Sp, t));
    private static Formula Degree(Formula g, Formula v) =>
        Cast(Apply(Qualified("SimpleGraph", "degree"), g, v), Reals());
    private static Formula GraphBinders(Formula body) => All("n", Naturals(),
        All("G", GraphType(), Instance(Call("DecidableRel", Adj(F.Id("G"))), body)));
    private static Formula EdgeTerm(Formula g, Formula u, Formula v) => new Formula.Fraction(
        Apply(Qualified("Real", "sqrt"),
            Add(new Formula.Power(Degree(g, u), D(2)), new Formula.Power(Degree(g, v), D(2)))),
        Call("max", Degree(g, u), Degree(g, v)));
    private static Formula LambdaEndpoint(string name, Formula body) => Seq(LambdaLower, Sp,
        Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, Call("Fin", F.Id("n")))),
        Sp, Mapsto, Sp, body);

    private static Formula CdsoFormula()
    {
        Formula g = F.Id("G"), u = F.Id("u"), v = F.Id("v"), e = F.Id("e");
        Formula symmetry = All("u", Call("Fin", F.Id("n")), All("v", Call("Fin", F.Id("n")),
            Equal(EdgeTerm(g, u, v), EdgeTerm(g, v, u))));
        Formula function = LambdaEndpoint("u", LambdaEndpoint("v", EdgeTerm(g, u, v)));
        Formula pair = Seq(Langle, function, Comma, Sp, F.Id("h"), Rangle);
        Formula summand = Apply(Apply(Qualified("Sym2", "lift"), pair), e);
        Formula sum = Seq(Sum, Underscore, Grp(Seq(e, Sp, InMacro, Sp, Edges(g))), Sp, summand);
        return Disp(GraphBinders(All("h", symmetry, Equal(Index(g), sum))));
    }

    private static Formula CyclomaticFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), k = F.Id("k"), s = F.Id("s");
        Formula pairType = Call("Sym2", Call("Fin", n));
        Formula subset = Seq(s, Sp, Subseteq, Sp, Edges(g));
        Formula card = Equal(Apply(Qualified("Finset", "card"), s), k);
        Formula deleted = Apply(Qualified("SimpleGraph", "deleteEdges"), g,
            Cast(s, Call("Set", pairType)));
        Formula acyclic = Apply(Qualified("SimpleGraph", "IsAcyclic"), deleted);
        Formula member = Some("s", Call("Finset", pairType), And(subset, And(card, acyclic)));
        Formula set = Seq(OpenBrace, k, Sp, Colon, Sp, Naturals(), Sp, Mid, Sp, member, CloseBrace);
        return Disp(GraphBinders(Equal(Cyclomatic(g), Call("sInf", set))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), ell = F.Id("ell"), g = F.Id("G"), h = F.Id("H");
        Formula minimum = All("H", GraphType(), Instance(Call("DecidableRel", Adj(h)),
            Imp(Connected(h), Imp(Equal(Cyclomatic(h), ell), LeqTo(Index(g), Index(h))))));
        Formula universal = Some("v", Call("Fin", n), All("w", Call("Fin", n),
            Imp(new Formula.Not(Equal(F.Id("w"), F.Id("v"))),
                Apply(Qualified("SimpleGraph", "Adj"), g, F.Id("v"), F.Id("w")))));
        Formula graphs = All("G", GraphType(), Instance(Call("DecidableRel", Adj(g)),
            Imp(Connected(g), Imp(Equal(Cyclomatic(g), ell), Imp(minimum, universal)))));
        Formula quantified = All("n", Naturals(), All("ell", Naturals(), Imp(LeqTo(D(1), ell), graphs)));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(quantified)));
    }
}
