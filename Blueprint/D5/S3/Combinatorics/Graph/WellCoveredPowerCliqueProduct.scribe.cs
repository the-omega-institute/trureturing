using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class WellCoveredPowerCliqueProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/WellCoveredPowerCliqueProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cartesian products with a sufficiently large clique preserve well-covered powers and increase the diameter by one. Starting from the seven-cycle gives arbitrary diameters at least three.",
        H("Well-covered powers with unbounded diameter"),
        Blocks(
            Node("power", "Graph powers", "power", DescribeRole.Definition,
                "The d-th power joins distinct vertices whose graph distance is at most d. Only connected finite graphs are used."),
            Node("maximal-independent", "Maximal independent finite sets", "IsMaximalIndep", DescribeRole.Definition,
                "The set is independent and every vertex outside it has a neighbor inside it. This is precisely maximality under inclusion."),
            Node("well-covered", "Well-covered graphs", "WellCovered", DescribeRole.Definition,
                "Any two maximal independent finite sets have equal cardinalities, equivalently all minimal vertex covers have the same cardinality."),
            Node("all-powers", "Connected graphs with well-covered powers", "WCP", DescribeRole.Definition,
                "The graph is connected and its d-th power is well-covered for every positive integer d."),
            Node("product-distance", "Distance in a clique product", "distance_cliqueProduct", DescribeRole.Theorem,
                "In G □ K_t the distance from (u,a) to (v,b) is dist_G(u,v) plus zero when a=b and one otherwise."),
            Node("projected-maximality", "Maximality survives projection", "projection_maximal", DescribeRole.Theorem,
                "For d at least one and t greater than the number of vertices of G, a maximal independent set of (G □ K_t)^d projects to a maximal independent set of G^(d-1). If an omitted base vertex could be added, choose a clique label absent from the original set. Its distance to every selected point is then greater than d, contradicting maximality."),
            Node("product-powers", "Clique products preserve well-covered powers", "wcp_cliqueProduct", DescribeRole.Theorem,
                "Let G be a finite connected graph all of whose positive powers are well-covered. If t exceeds its order, then G □ K_t also has this property. Projection is injective on each independent set and preserves cardinality. The zero-th power is edgeless and has a single maximal independent set."),
            Node("product-diameter", "Clique products increase diameter", "diam_cliqueProduct", DescribeRole.Theorem,
                "If t is at least two, the diameter of G □ K_t is diam(G)+1. A pair attaining diam(G), equipped with two different clique labels, attains this bound."),
            Node("seven-cycle", "The seven-cycle has well-covered powers", "cycle_seven_wcp", DescribeRole.Theorem,
                "The cyclic distance on Fin 7 is min(|u-v|,7-|u-v|). It gives the seven-cycle. The maximal independent sets of its first, second and third powers have cardinalities three, two and one. All higher powers equal the third."),
            Node("all-diameters", "Every diameter at least three occurs", "exists_wcp_diameter", DescribeRole.Theorem,
                "For every natural number D at least three there exists a finite connected graph with well-covered positive powers and diameter D. The initial graph is the seven-cycle. At each step take the Cartesian product with the clique of order one greater than the current graph's order."),
            Node("diameter-claim", "The proposed diameter bound", "claim", DescribeRole.Definition,
                "Question 3.9 asks: Let G be a simple connected graph such that G^d is well-covered for all d at least one. Is it true that diam(G) is at most three? The quantified statement ranges over every finite vertex type and every simple graph on it."),
            Describe.Lean(
                DescribeId.Create("diameter-refuted"), DeclarationHandle.Create(Prefix + "result"),
                H("The diameter bound is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The seven-cycle □ K_8 has 56 vertices, well-covered positive powers and diameter four. It refutes the proposed bound."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("pham-vu-2026-well-covered-powers-diameter"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Statement(declaration))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Id(string x) => F.Id(x);
    private static Formula Call(string x, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. args]);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Ex(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Type() => new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula ExistsInstance(Formula type, Formula body) =>
        Seq(Exists, Sp, OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Graphs(Formula body) => All("V", Type(),
        Instance(Call("Fintype", Id("V")), Instance(Call("DecidableEq", Id("V")),
            All("G", Call("SimpleGraph", Id("V")), body))));
    private static Formula Product() => Call("boxProd", Id("G"), Call("completeGraph", Call("Fin", Id("t"))));
    private static Formula Statement(string name)
    {
        var g = Id("G"); var d = Id("d"); var t = Id("t");
        var u = Id("u"); var v = Id("v"); var i = Id("I"); var j = Id("J");
        var V = Id("V"); var h = Product();
        var ig = Call("IsMaximalIndep", g, i);
        var positive = Le(D(1), d);
        var big = Call("LT", Call("FintypeCard", V), t);
        var finiteSet = Call("Finset", V);
        var maximal = And(
            All("u", V, Imp(Call("mem", u, i), All("v", V,
                Imp(And(Call("mem", v, i), Ne(u, v)), Not(Call("Adj", g, u, v)))))),
            All("v", V, Imp(Not(Call("mem", v, i)), Ex("u", V,
                And(Call("mem", u, i), Call("Adj", g, v, u))))));
        var bound = Graphs(Instance(Call("DecidableRel", Call("Adj", g)),
            Imp(Call("WCP", g), Le(Call("diam", g), D(3)))));
        return name switch
        {
            "power" => Graphs(All("d", Nat(), All("u", V, All("v", V,
                Iff(Call("Adj", Call("power", g, d), u, v),
                    And(Ne(u, v), Le(Call("dist", g, u, v), d))))))),
            "IsMaximalIndep" => Graphs(All("I", finiteSet, Iff(ig, maximal))),
            "WellCovered" => Graphs(Iff(Call("WellCovered", g),
                All("I", finiteSet, All("J", finiteSet,
                    Imp(And(ig, Call("IsMaximalIndep", g, j)), Eq(Call("card", i), Call("card", j))))))),
            "WCP" => Graphs(Iff(Call("WCP", g), And(Call("Connected", g),
                All("d", Nat(), Imp(positive, Call("WellCovered", Call("power", g, d))))))),
            "distance_cliqueProduct" => Graphs(All("t", Nat(), Imp(Call("Connected", g),
                All("x", Call("Prod", V, Call("Fin", t)), All("y", Call("Prod", V, Call("Fin", t)),
                    Eq(Call("dist", h, Id("x"), Id("y")),
                        Add(Call("dist", g, Call("fst", Id("x")), Call("fst", Id("y"))),
                            Call("if", Eq(Call("snd", Id("x")), Call("snd", Id("y"))), D(0), D(1))))))))),
            "projection_maximal" => Graphs(All("t", Nat(), All("d", Nat(),
                All("I", Call("Finset", Call("Prod", V, Call("Fin", t))),
                    Imp(And(Call("Connected", g), And(big, And(positive,
                        Call("IsMaximalIndep", Call("power", h, d), i)))),
                        Call("IsMaximalIndep", Call("power", g, Sub(d, D(1))), Call("imageFst", i))))))),
            "wcp_cliqueProduct" => Graphs(All("t", Nat(), Imp(And(Call("WCP", g), big), Call("WCP", h)))),
            "diam_cliqueProduct" => Graphs(All("t", Nat(), Imp(And(Call("Connected", g), Le(D(2), t)),
                Eq(Call("diam", h), Add(Call("diam", g), D(1)))))),
            "cycle_seven_wcp" => Call("WCP", Call("cycle", D(7))),
            "exists_wcp_diameter" => All("D", Nat(), Imp(Le(D(3), Id("D")),
                Ex("V", Type(), ExistsInstance(Call("Fintype", V), ExistsInstance(Call("DecidableEq", V),
                    Ex("G", Call("SimpleGraph", V), And(Call("WCP", g), Eq(Call("diam", g), Id("D"))))))))),
            "claim" => Iff(Id("claim"), bound),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name))
        };
    }
}
