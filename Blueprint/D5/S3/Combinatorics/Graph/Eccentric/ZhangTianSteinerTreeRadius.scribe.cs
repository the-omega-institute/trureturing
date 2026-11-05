using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Eccentric;

internal sealed class ZhangTianSteinerTreeRadiusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/zhangtian2025steinerradius");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal-cut averaging proves Zhang–Tian Conjecture 5.1 for every finite tree.",
        H("Steiner diameter and anchored radius of trees"),
        Blocks(
            Node("steinerDist", "Steiner distance", DistanceFormula(),
                "Page 2: \"The Steiner distance d_G(S) among the vertices of S (or simply the distance of S) is defined as the minimum size among all connected subgraphs whose vertex sets contain S.\" "
                    + "The size of a graph is its number of edges. The natural infimum ranges over actual connected subgraphs, recording both vertices and edges. "
                    + "The displayed set coercion views the finite terminal set as a set of vertices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("steinerEcc", "Steiner vertex eccentricity", EccentricityFormula(),
                "Page 2: \"The Steiner k-eccentricity ε_k(v; G) of a vertex v in G is defined by max{d_G(S) : v ∈ S ⊆ V(G), |S| = k}, where k ≥ 2.\" "
                    + "Finite subsets of the vertex type express S ⊆ V(G); their cardinality is the number of terminals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("steinerDiam", "Steiner diameter", DiameterFormula(),
                "Page 2: \"The Steiner k-radius of G is Sr_k(G) = min{ε_k(v) : v ∈ V(G)}, and the Steiner k-diameter of G is Sd_k(G) = max{ε_k(v) : v ∈ V(G)}.\" "
                    + "steinerDiam is the natural supremum of the vertex eccentricities; the radius mentioned in this source sentence is not a separate definition here.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("steinerSetEcc", "Anchored Steiner eccentricity", SetEccentricityFormula(),
                "Page 2: \"The Steiner (k, k′)-eccentricity ε_{k,k′}(S′; G) of a k′-subset S′ in G is defined as the maximum Steiner distance over k-subsets of V(G) that include S′, that is, ε_{k,k′}(S′; G) = max{d_G(S) : S′ ⊆ S ⊆ V(G), |S| = k}, where k ≥ 2 and k ≥ k′ ≥ 1.\" "
                    + "The anchor cardinality is supplied by the theorem hypotheses, while steinerSetEcc takes the anchor set itself.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("steinerRadius", "Anchored Steiner radius", RadiusFormula(),
                "Page 2: \"The Steiner (k, k′)-radius of G is Sr_{k,k′}(G) = min{ε_{k,k′}(S′; G) : S′ ⊆ V(G), |S′| = k′}, where k′ ≥ 1.\" "
                    + "steinerRadius takes the natural infimum over every anchor set of the specified cardinality.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Zhang–Tian Conjecture 5.1", Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, ClaimBody())),
                "Conjecture 5.1, page 14: \"Let n, k, k′ be integers with n ≥ k ≥ 3 and k > k′ ≥ 1 and let T be a tree with order n. Then Sd_k(T) ≤ k/(k − k′) Sr_{k,k′}(T) − k′(k′ − 1)/(k − k′).\" "
                    + "Here n is Fintype.card V and r denotes k′. Natural-valued distances, k and r are cast into ℚ before the displayed divisions and subtractions. "
                    + "Finiteness and decidable equality appear as anonymous instance arguments; IsTree means connected and acyclic.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Separates", "Terminal separation after edge deletion", SeparatesFormula(),
                "Separates T S e means that deleting e disconnects two terminals of S. No choice of an orientation or a component is part of this predicate.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("cutEdges", "Separating edges", CutEdgesFormula(),
                "cutEdges filters the graph's finite edge set by terminal separation. Each undirected edge is counted once as an element of Sym2 V.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("steinerDist_cut", "Distance counts separating edges", CutTheoremFormula(),
                "For a finite tree and a nonempty terminal set, the defining minimum equals the number of separating edges. "
                    + "The intersection of all connected terminal-containing subgraphs is connected because the tree has a unique path between any two vertices. "
                    + "An edge in that intersection separates terminals: otherwise the deletion component containing a chosen terminal contains all terminals and excludes the edge.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("pointwise_bound", "A bound for every pair of terminal sets", PointwiseFormula(),
                "For every k-set A and r-set B in a finite tree, with 1 ≤ r < k and enough vertices, "
                    + "(k−r) steinerDist T A + r steinerDist T B ≤ k steinerSetEcc T k B. "
                    + "Every edge of the B-hull persists when B is enlarged. For each edge of the A-hull outside it, select an A-terminal separated from a B-terminal. "
                    + "That edge persists whenever the selected terminal belongs to a sampled (k−r)-subset of A. Double counting these samples yields the inequality. "
                    + "The sets may overlap, and A need not maximize the distance.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The conjecture holds for all finite trees", Disp(ClaimBody()),
                "Choose terminal sets attaining the Steiner diameter and the anchored radius. "
                    + "The pointwise inequality retains the entire anchor hull, whose edge count is at least r−1. "
                    + "This supplies the additive r(r−1) correction. Division by the positive rational k−r gives the displayed inequality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-tian-2025-steiner-diameter-radius-trees"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name switch {
                "steinerDist" => "zt-distance", "steinerEcc" => "zt-eccentricity",
                "steinerDiam" => "zt-diameter", "steinerSetEcc" => "zt-set-eccentricity",
                "steinerRadius" => "zt-radius", "Separates" => "zt-separates",
                "cutEdges" => "zt-cut-edges", "steinerDist_cut" => "zt-cut-characterization",
                "pointwise_bound" => "zt-pointwise", _ => "zt-" + name
            }), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Projection(Formula value, string name) => Seq(value, Dot, F.Id(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula ImpliesFormula(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeFormula(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtFormula(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mem(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula SubsetFormula(Formula left, Formula right) => Seq(left, Sp, Subseteq, Sp, right);
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, Sp, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, Sp, CloseBrace);
    private static Formula Singleton(Formula value) => Seq(OpenBrace, value, CloseBrace);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula GraphBinders(Formula body) => All("V", F.Id("Type"), All("G", Call("SimpleGraph", F.Id("V")), body));
    private static Formula TerminalBinders(Formula body) => GraphBinders(All("S", Call("Finset", F.Id("V")), body));

    private static Formula DistanceFormula()
    {
        Formula g = F.Id("G"), s = F.Id("S"), h = F.Id("H"), m = F.Id("m");
        Formula witnesses = Some("H", Projection(g, "Subgraph"),
            And(Projection(h, "Connected"), And(SubsetFormula(Cast(s, Call("Set", F.Id("V"))), Projection(h, "verts")),
                Equal(Projection(Projection(h, "edgeSet"), "ncard"), m))));
        return Disp(TerminalBinders(Equal(Call("steinerDist", g, s), Call("sInf", SetOf("m", Naturals(), witnesses)))));
    }

    private static Formula EccentricityFormula()
    {
        Formula g = F.Id("G"), k = F.Id("k"), v = F.Id("v"), s = F.Id("S"), m = F.Id("m");
        Formula witnesses = Some("S", Call("Finset", F.Id("V")),
            And(Mem(v, s), And(Equal(Projection(s, "card"), k), Equal(Call("steinerDist", g, s), m))));
        return Disp(GraphBinders(All("k", Naturals(), All("v", F.Id("V"),
            Equal(Call("steinerEcc", g, k, v), Call("sSup", SetOf("m", Naturals(), witnesses)))))));
    }

    private static Formula DiameterFormula()
    {
        Formula g = F.Id("G"), k = F.Id("k"), m = F.Id("m");
        Formula witnesses = Some("v", F.Id("V"), Equal(Call("steinerEcc", g, k, F.Id("v")), m));
        return Disp(GraphBinders(All("k", Naturals(),
            Equal(Call("steinerDiam", g, k), Call("sSup", SetOf("m", Naturals(), witnesses))))));
    }

    private static Formula SetEccentricityFormula()
    {
        Formula g = F.Id("G"), k = F.Id("k"), b = F.Id("B"), s = F.Id("S"), m = F.Id("m");
        Formula witnesses = Some("S", Call("Finset", F.Id("V")),
            And(SubsetFormula(b, s), And(Equal(Projection(s, "card"), k), Equal(Call("steinerDist", g, s), m))));
        return Disp(GraphBinders(All("k", Naturals(), All("B", Call("Finset", F.Id("V")),
            Equal(Call("steinerSetEcc", g, k, b), Call("sSup", SetOf("m", Naturals(), witnesses)))))));
    }

    private static Formula RadiusFormula()
    {
        Formula g = F.Id("G"), k = F.Id("k"), r = F.Id("r"), b = F.Id("B"), m = F.Id("m");
        Formula witnesses = Some("B", Call("Finset", F.Id("V")),
            And(Equal(Projection(b, "card"), r), Equal(Call("steinerSetEcc", g, k, b), m)));
        return Disp(GraphBinders(All("k", Naturals(), All("r", Naturals(),
            Equal(Call("steinerRadius", g, k, r), Call("sInf", SetOf("m", Naturals(), witnesses)))))));
    }

    private static Formula SeparatesFormula()
    {
        Formula t = F.Id("G"), s = F.Id("S"), e = F.Id("e"), a = F.Id("a"), b = F.Id("b");
        Formula deleted = Apply(Projection(t, "deleteEdges"), Singleton(e));
        Formula unreachable = Seq(Neg, Sp, Parenthesized(Apply(Projection(Parenthesized(deleted), "Reachable"), a, b)));
        Formula rhs = Some("a", F.Id("V"), And(Mem(a, s), Some("b", F.Id("V"), And(Mem(b, s), unreachable))));
        return Disp(TerminalBinders(All("e", Call("Sym2", F.Id("V")),
            Logic(Call("Separates", t, s, e), FormulaLogicOperator.Iff, rhs))));
    }

    private static Formula CutEdgesFormula()
    {
        Formula v = F.Id("V"), t = F.Id("T"), s = F.Id("S");
        Formula rhs = Apply(Qualified("Finset", "filter"), Call("Separates", t, s), Projection(t, "edgeFinset"));
        return Disp(All("V", F.Id("Type"), Instance(Call("Fintype", v),
            All("T", Call("SimpleGraph", v), All("S", Call("Finset", v), Equal(Call("cutEdges", t, s), rhs))))));
    }

    private static Formula CutTheoremFormula()
    {
        Formula v = F.Id("V"), t = F.Id("T"), s = F.Id("S");
        Formula conclusion = Equal(Call("steinerDist", t, s), Projection(Parenthesized(Call("cutEdges", t, s)), "card"));
        return Disp(All("V", F.Id("Type"), Instance(Call("Fintype", v), Instance(Call("DecidableEq", v),
            All("T", Call("SimpleGraph", v), ImpliesFormula(Projection(t, "IsTree"), All("S", Call("Finset", v),
                ImpliesFormula(Projection(s, "Nonempty"), conclusion))))))));
    }

    private static Formula PointwiseFormula()
    {
        Formula v = F.Id("V"), t = F.Id("T"), a = F.Id("A"), b = F.Id("B"), k = F.Id("k"), r = F.Id("r");
        Formula conclusion = LeFormula(Add(Multiply(Parenthesized(Subtract(k, r)), Call("steinerDist", t, a)),
            Multiply(r, Call("steinerDist", t, b))), Multiply(k, Call("steinerSetEcc", t, k, b)));
        Formula body = ImpliesFormula(Equal(Projection(a, "card"), k),
            ImpliesFormula(Equal(Projection(b, "card"), r), ImpliesFormula(LtFormula(r, k),
                ImpliesFormula(LeFormula(D(1), r), ImpliesFormula(LeFormula(k, Apply(Qualified("Fintype", "card"), v)), conclusion)))));
        return Disp(All("V", F.Id("Type"), Instance(Call("Fintype", v), Instance(Call("DecidableEq", v),
            All("T", Call("SimpleGraph", v), ImpliesFormula(Projection(t, "IsTree"),
                All("A", Call("Finset", v), All("B", Call("Finset", v), All("k", Naturals(), All("r", Naturals(), body))))))))));
    }

    private static Formula ClaimBody()
    {
        Formula v = F.Id("V"), t = F.Id("T"), k = F.Id("k"), r = F.Id("r");
        Formula kq = Cast(k, Rationals()), rq = Cast(r, Rationals());
        Formula denominator = Subtract(kq, rq);
        Formula rhs = Subtract(Multiply(new Formula.Fraction(kq, denominator), Cast(Call("steinerRadius", t, k, r), Rationals())),
            new Formula.Fraction(Multiply(rq, Parenthesized(Subtract(rq, D(1)))), denominator));
        Formula body = ImpliesFormula(Projection(t, "IsTree"),
            ImpliesFormula(LeFormula(k, Apply(Qualified("Fintype", "card"), v)),
                ImpliesFormula(LeFormula(D(3), k), ImpliesFormula(LtFormula(r, k),
                    ImpliesFormula(LeFormula(D(1), r), LeFormula(Cast(Call("steinerDiam", t, k), Rationals()), rhs))))));
        return All("V", F.Id("Type"), Instance(Call("Fintype", v), Instance(Call("DecidableEq", v),
            All("T", Call("SimpleGraph", v), All("k", Naturals(), All("r", Naturals(), body))))));
    }
}
