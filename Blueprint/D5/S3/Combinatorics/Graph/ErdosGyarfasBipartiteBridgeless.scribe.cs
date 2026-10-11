using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ErdosGyarfasBipartiteBridgelessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A minimal bipartite graph of minimum degree at least three without a "
            + "power-of-two cycle is connected and has no bridge.",
        H("Minimal bipartite Erdős–Gyárfás counterexamples have no bridge"),
        Blocks(
            Node("power-two-cycle", "Power-of-two cycles", "HasPowTwoCycle",
                PowerCycleFormula(),
                "The allowed exponents are the natural numbers at least two, "
                    + "so the excluded cycle lengths are four, eight, sixteen, and so on.",
                DescribeRole.Definition),
            Node("bipartite-counterexample", "Bipartite counterexamples", "IsBipCounterexample",
                CounterexampleFormula(),
                "The vertex type is nonempty, the graph admits a proper two-colouring, "
                    + "every degree is at least three, and no cycle has an allowed length.",
                DescribeRole.Definition),
            Node("minimal-counterexample", "Lexicographic minimality", "IsMinimalBipCounterexample",
                MinimalFormula(),
                "Compare with every counterexample on every finite vertex type. "
                    + "The vertex count is minimal, and among equal vertex counts the edge count is minimal.",
                DescribeRole.Definition),
            Node("two-edge-connectivity", "Two-edge-connectivity assertion", "claim",
                ClaimFormula(),
                "Every minimal bipartite counterexample is connected, and deleting "
                    + "any one of its edges leaves a connected graph.",
                DescribeRole.Definition),
            Node("connected", "Minimal counterexamples are connected", "minimal_connected",
                Disp(GraphContext("V", "G", Imp(Call("IsMinimalBipCounterexample", F.Id("G")),
                    Call("Connected", F.Id("G"))))),
                "An induced connected component retains every vertex degree. "
                    + "Its inclusion preserves the colouring and all cycle lengths. "
                    + "A proper component would therefore be a counterexample with fewer vertices.",
                DescribeRole.Theorem),
            Node("bridgeless", "Minimal counterexamples have no bridge", "result",
                Disp(F.Id("claim")),
                "Contract a bridge and exchange the two colours on one component. "
                    + "Every retained degree is at least three, while the merged vertex "
                    + "has degree at least four. A cycle stays on one side of the merged "
                    + "vertex and lifts to a cycle of the original graph of equal length. "
                    + "The contracted graph has fewer vertices, contradicting minimality.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("ducoffe-dumitru-2026-bipartite-minimal-two-edge-connected"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Constant(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula GraphContext(string vertex, string graph, Formula body,
        bool finite = true)
    {
        var v = F.Id(vertex); var g = F.Id(graph);
        var graphBody = finite
            ? Seq(OpenBracket, Call("DecidableRel", Call("Adj", g)), CloseBracket, Sp, body)
            : body;
        var graphBinder = All(graph, Call("SimpleGraph", v), graphBody);
        var vertexBody = finite
            ? Seq(OpenBracket, Call("Fintype", v), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", v), CloseBracket, Sp, graphBinder)
            : graphBinder;
        return All(vertex, Constant("Type"), vertexBody);
    }

    private static Formula PowerCycleFormula()
    {
        var g = F.Id("G"); var v = F.Id("v"); var c = F.Id("c"); var k = F.Id("k");
        return Disp(GraphContext("V", "G", Iff(Call("HasPowTwoCycle", g),
            Exists("v", F.Id("V"), Exists("c", Call("Walk", g, v, v),
                And(Call("IsCycle", c), Exists("k", Constant("Nat"),
                    And(Le(D(2), k), Eq(Call("length", c),
                        new Formula.Power(D(2), k)))))))), false));
    }

    private static Formula CounterexampleFormula()
    {
        var g = F.Id("G"); var v = F.Id("v");
        return Disp(GraphContext("V", "G", Iff(Call("IsBipCounterexample", g),
            And(Call("Nonempty", F.Id("V")), And(Call("Colorable", g, D(2)),
                And(All("v", F.Id("V"), Le(D(3), Call("degree", g, v))),
                    new Formula.Not(Call("HasPowTwoCycle", g))))))));
    }

    private static Formula MinimalFormula()
    {
        var v = F.Id("V"); var w = F.Id("W"); var g = F.Id("G"); var h = F.Id("H");
        var comparison = Or(Lt(Call("card", v), Call("card", w)),
            And(Eq(Call("card", v), Call("card", w)),
                Le(Call("card", Call("edgeFinset", g)), Call("card", Call("edgeFinset", h)))));
        return Disp(GraphContext("V", "G", Iff(Call("IsMinimalBipCounterexample", g),
            And(Call("IsBipCounterexample", g),
                GraphContext("W", "H", Imp(Call("IsBipCounterexample", h), comparison))))));
    }

    private static Formula ClaimFormula()
    {
        var g = F.Id("G"); var e = F.Id("e");
        var singleton = Seq(OpenBrace, e, CloseBrace);
        var conclusion = And(Call("Connected", g), All("e", Call("Sym2", F.Id("V")),
            Imp(Seq(e, Sp, InMacro, Sp, Call("edgeSet", g)),
                Call("Connected", Call("deleteEdges", g, singleton)))));
        return Disp(Iff(F.Id("claim"), GraphContext("V", "G",
            Imp(Call("IsMinimalBipCounterexample", g), conclusion))));
    }
}
