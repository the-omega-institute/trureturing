using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class TwoTreeStretchSeparationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Chordal/TwoTreeStretchSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive two-trees have unbounded optimal spanning-tree stretch and bounded gain errors.",
        H("Spanning-tree stretch and gain reconstruction on recursive two-trees"),
        Blocks(
            Paragraph(Text("Start with an oriented triangle. At each round attach a new vertex to both endpoints of each edge born in the preceding round. The two child edges follow the direction of the path through the new vertex, and the parent edge remains.")),
            Entry("two-tree-edge-count", "twoTree_edge_count", "Edge count",
                EdgeCount(), "Each fresh vertex introduces two edges, and the earlier edges persist."),
            Entry("two-tree-chordal", "twoTree_isChordal", "Chordality and connectivity",
                Depth(And(Call("IsChordal", Graph), And(Call("Connected", Graph),
                    Eqn(Call("card", Vertices), Mul(D(3), Call("pow", D(2), F.Id("d"))))))),
                "Each fresh vertex has two adjacent neighbors. A cycle of length at least four that visits it has a chord between those neighbors. The old graph is induced and every new vertex joins it."),
            Entry("two-tree-stretch", "twoTree_min_spanning_tree_stretch_eq", "Exact spanning-tree stretch",
                Stretch(), "Suppress the newest vertices in a spanning tree by contracting one incident edge at each new vertex. The resulting tree on the preceding round has a frontier edge whose distance is at least the previous lower bound. The fresh vertex on that edge has only one tree neighbor, so one child edge has distance at least one larger. For the upper bound, attach each new vertex as a leaf to the source of its parent edge."),
            Entry("two-tree-group-gains", "twoTree_exists_one_approximate_gain_potential", "Reconstruction with coefficient one",
                GroupGains(), "Fit two core edges exactly. At a fresh vertex, transport a potential along the parent edge and then along its second child edge. The two new errors are controlled by the triangle defect and the previous error on the parent edge."),
            Entry("two-tree-integral-obstruction", "twoTree_integer_lower_bound_one", "An integral obstruction",
                Integral(), "Assign unit oriented sum to each triangle. If every integral residual had absolute value less than one, the sum of the frontier residuals would vanish, contradicting the positive sum of the triangle defects."),
            Describe.Lean(
                DescribeId.Create("two-tree-banach-value"),
                DeclarationHandle.Create(Module + "twoTreeBanachConstant"),
                H("Reconstruction radius"),
                StatementSource.FromAuthor(Disp(Depth(Eqn(Bound,
                    Sub(D(1), new Formula.Fraction(D(2), Mul(D(3), new Formula.Power(D(2), F.Id("d"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The value at depth zero is one third. A new round takes the average of the previous value and one."))),
                DescribeRole.Definition),
            Entry("two-tree-banach-constant", "twoTree_banach_exact_constant", "Exact real Banach constant",
                Banach(), "The sum of the frontier residuals equals the sum of the oriented triangle coordinates. In the sum norm this gives a lower bound on a single frontier edge. The upper bound divides the core defect into thirds and assigns each fresh potential the midpoint of its two proposed values."))));

    private static DocumentBlock Entry(string id, string name, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pair(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Instance(Formula f) => Seq(OpenBracket, f, CloseBracket, Sp);
    private static Formula Depth(Formula f) => All("d", Call("Nat"), f);
    private static Formula Vertices => Call("TwoTreeV", F.Id("d"));
    private static Formula Graph => Call("twoTree", F.Id("d"));
    private static Formula Bound => Call("twoTreeBanachConstant", F.Id("d"));

    private static Formula EdgeCount()
    {
        var d = F.Id("d");
        return Depth(Eqn(Call("card", Call("edgeSet", Graph)),
            Mul(D(3), P(Sub(Call("pow", D(2), Add(d, D(1))), D(1))))));
    }

    private static Formula Stretch()
    {
        var t = F.Id("T");
        var u = F.Id("u");
        var v = F.Id("v");
        var tree = Call("SimpleGraph", Vertices);
        var bound = Add(F.Id("d"), D(2));
        var lower = All("T", tree, Imp(Le(t, Graph), Imp(Call("IsTree", t),
            Some("u", Vertices, Some("v", Vertices,
                And(Adj(u, v), Le(bound, Call("edist", t, u, v))))))));
        var upper = Some("T", tree, And(Le(t, Graph), And(Call("IsTree", t),
            All("u", Vertices, All("v", Vertices,
                Imp(Adj(u, v), Le(Call("edist", t, u, v), bound)))))));
        return Depth(And(lower, upper));
    }

    private static Formula Adj(Formula u, Formula v) => Call("Adj", Graph, u, v);
    private static Formula Gain(Formula u, Formula v) => Call("g", u, v);
    private static Formula Phi(Formula u) => Call("phi", u);

    private static Formula Reverse(bool multiplicative)
    {
        var u = F.Id("u");
        var v = F.Id("v");
        var inv = multiplicative ? Call("inv", Gain(u, v)) : Call("neg", Gain(u, v));
        return All("u", Vertices, All("v", Vertices, Imp(Adj(u, v), Eqn(Gain(v, u), inv))));
    }

    private static Formula Triangle(bool multiplicative, Formula bound)
    {
        var u = F.Id("u");
        var v = F.Id("v");
        var w = F.Id("w");
        var error = multiplicative
            ? Call("dist", Mul(Gain(u, v), Gain(v, w)), Gain(u, w))
            : Call("norm", Sub(Add(Gain(u, v), Gain(v, w)), Gain(u, w)));
        return All("u", Vertices, All("v", Vertices, All("w", Vertices,
            Imp(Adj(u, v), Imp(Adj(v, w), Imp(Adj(u, w), Le(error, bound)))))));
    }

    private static Formula Error(Formula u, Formula v) => Call("norm", Sub(Gain(u, v), Sub(Phi(v), Phi(u))));

    private static Formula AllEdges(Func<Formula, Formula, Formula> body)
    {
        var u = F.Id("u");
        var v = F.Id("v");
        return All("u", Vertices, All("v", Vertices, Imp(Adj(u, v), body(u, v))));
    }

    private static Formula GainType(Formula e) => Pair(Vertices, Pair(Vertices, e));

    private static Formula GroupGains()
    {
        var h = F.Id("H");
        var epsilon = F.Id("epsilon");
        var result = Some("phi", Pair(Vertices, h), AllEdges((u, v) => Le(
            Call("dist", Gain(u, v), Mul(Call("inv", Phi(u)), Phi(v))), epsilon)));
        return All("ell", Call("Universe"), Depth(All("H", Call("Type", F.Id("ell")),
            Seq(Instance(Call("Group", h)), Instance(Call("PseudoMetricSpace", h)),
                Instance(Call("IsIsometricSMul", h, h)),
                Instance(Call("IsIsometricSMul", Call("MulOpposite", h), h)), Comma, Sp,
                All("g", GainType(h), All("epsilon", Call("Real"), Imp(Le(D(0), epsilon),
                    Imp(Reverse(true), Imp(Triangle(true, epsilon), result)))))))));
    }

    private static Formula Integral()
    {
        var z = Call("Int");
        var u = F.Id("u");
        var v = F.Id("v");
        var obstruction = All("phi", Pair(Vertices, z),
            Some("u", Vertices, Some("v", Vertices, And(Adj(u, v), Le(D(1), Error(u, v))))));
        return Depth(Some("g", GainType(z), And(Reverse(false), And(Triangle(false, D(1)), obstruction))));
    }

    private static Formula Banach()
    {
        var e = F.Id("E");
        var epsilon = F.Id("epsilon");
        var u = F.Id("u");
        var v = F.Id("v");
        var w = F.Id("w");
        var d = F.Id("d");
        var real = Call("Real");
        var cycles = Call("TwoTreeCycles", d);
        Formula canonical(Formula a, Formula b) => Call("twoTreeCanonicalGain", d, a, b);
        var reverse = AllEdges((a, b) => Eqn(canonical(b, a), Call("neg", canonical(a, b))));
        var flat = All("u", Vertices, All("v", Vertices, All("w", Vertices,
            Imp(Adj(u, v), Imp(Adj(v, w), Imp(Adj(u, w), Le(
                Call("norm", Sub(Add(canonical(u, v), canonical(v, w)), canonical(u, w))), D(1))))))));
        var lower = All("phi", Pair(Vertices, cycles), Some("u", Vertices, Some("v", Vertices,
            And(Adj(u, v), Le(Bound, Call("norm", Sub(canonical(u, v), Sub(Phi(v), Phi(u)))))))));
        var upper = All("E", Call("Type", F.Id("ell")),
            Seq(Instance(Call("SeminormedAddCommGroup", e)), Instance(Call("NormedSpace", real, e)),
                Comma, Sp, All("g", GainType(e), All("epsilon", real, Imp(Le(D(0), epsilon),
                    Imp(Reverse(false), Imp(Triangle(false, epsilon),
                        Some("phi", Pair(Vertices, e), AllEdges((a, b) =>
                            Le(Error(a, b), Mul(Bound, epsilon)))))))))));
        return All("ell", Call("Universe"), Depth(And(reverse, And(flat, And(lower, upper)))));
    }
}
