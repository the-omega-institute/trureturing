using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class AdjacentSupportPaymentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/AdjacentSupportPayment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a connected finite simple graph with maximum degree at most four and at most one original leaf neighbor per vertex, deleting two adjacent nonleaf supports with original pendant neighbors decreases the rational harmonic index by at least 21/20. All degrees in the remaining graph are recomputed, and original pendant edges at retained vertices contribute their actual defect changes.",
        H("Adjacent supports and harmonic payment"),
        Blocks(
            Definition("harmonic-index", "Harmonic index", "harmonicIndex",
                "For a finite simple graph F, H(F) is the sum of 2/(degree_F(x)+degree_F(y)) over its unordered edges xy. Isolated vertices contribute zero. The arithmetic is rational."),
            Definition("residual", "Actual induced residual", "residual",
                "The graph residual(G,X) is the induced graph on the subtype of vertices outside X. It retains every surviving vertex, including isolates, and computes its degrees from the surviving edges."),
            Definition("degree-defect", "Degree defect", "degreeDefect",
                "Write phi(d,e)=(d-e)^2/(2de(d+e)), with subtraction and division in the rational numbers. This expression is symmetric in d,e. On an edge both endpoint degrees are positive."),
            Definition("harmonic-defect", "Total harmonic defect", "harmonicDefect",
                "D(F) is the sum of phi(degree_F(x),degree_F(y)) over the unordered edges of F. Its degrees belong to F, including when F is an induced residual."),
            Definition("nonisolated-count", "Number of nonisolated vertices", "nonisolatedCount",
                "The nonisolated count of F is the cardinality of the vertices whose degree in F is nonzero."),
            Describe.Lean(
                DescribeId.Create("adjacent-support-harmonic-payment"),
                DeclarationHandle.Create(Prefix + "adjacent_support_harmonic_payment"),
                H("The simultaneous payment estimate"),
                StatementSource.FromAuthor(PaymentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every universe and finite vertex type V with decidable equality, let G be a simple graph with decidable adjacency. Assume G is connected, has maximum degree at most four, and every vertex has at most one neighbor of original G-degree one. Let a,b,u,v be vertices with a adjacent to b, degrees of a and b at least two, u of degree one adjacent to a, and v of degree one adjacent to b. Then H(G)-H(G[V\\{a,b}]) is at least 21/20. In the formula, leafCount(G,x) counts the neighbors of x with original degree one.")),
                    Paragraph(Text("Put X={a,b}. For a retained vertex x write q(x)=|N_G(x)\\X|, r(x)=|N_G(x) intersect X|, and t(x)=leafCount(G,x). The equality q+r=degree_G uses one joint loss at x; a shared neighbor has r=2. The two pendant vertices are distinct, survive, and become isolates. If i is the total number of residual isolates, reciprocal-degree accounting gives H(G)-H(G[V\\X])=(2+i)/2-(D(G)-D(G[V\\X])).")),
                    Paragraph(Text("For a retained original nonleaf vertex, the leaf-sensitive capacities c(d,t) for d=2,3,4 and t=0,1 are respectively (0,1/12), (1/30,1/10), and (3/40,13/120). The retained edge charges sum at most r(x)c(d,t); each original retained leaf edge uses its exact phi(d,1)-phi(q,1). Boundary charges cancel these capacities at retained vertices. At each deleted support, reserve its unique pendant edge and its edge to the other support, counting the latter by one half in each directed row. The resulting defect decrease is at most 19/20. Since i is at least two, the harmonic decrease is at least 2-19/20=21/20.")),
                    Paragraph(Text("A triangle abc with pendant edges au,bv,cw has H(G)=5/2 and H(G[V\\{a,b}])=1. The retained vertex c has joint loss two, and the retained edge cw has defect decrease 1/6, exceeding 1/15. This edge requires the original-leaf charge. Triangles and shared neighbors are allowed; no residual minimum-degree hypothesis is imposed."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Definition(string id, string title, string declaration,
        string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PaymentFormula()
    {
        var g = F.Id("G");
        var a = F.Id("a");
        var b = F.Id("b");
        var u = F.Id("u");
        var v = F.Id("v");
        var x = F.Id("x");
        var hypotheses = And(Call("Connected", g), And(Le(Call("maxDegree", g), F.D(4)),
            And(All("x", F.Id("V"), Le(Call("leafCount", g, x), F.D(1))),
            And(Call("Adj", g, a, b), And(Le(F.D(2), Call("degree", g, a)),
            And(Le(F.D(2), Call("degree", g, b)), And(Eq(Call("degree", g, u), F.D(1)),
            And(Call("Adj", g, a, u), And(Eq(Call("degree", g, v), F.D(1)),
                Call("Adj", g, b, v))))))))));
        var selected = F.Seq(F.OpenBrace, a, F.Comma, b, F.CloseBrace);
        var drop = F.Seq(Call("H", g), F.Minus, Call("H", Call("residual", g, selected)));
        var conclusion = Le(F.Seq(F.Frac, F.Grp(F.D(2, 1)), F.Grp(F.D(2, 0))), drop);
        Formula body = new Formula.Logic(Parenthesized(hypotheses),
            FormulaLogicOperator.Implies, Parenthesized(conclusion));
        foreach (var name in new[] { "v", "u", "b", "a" })
            body = All(name, F.Id("V"), body);
        return F.Disp(All("G", Call("SimpleGraph", F.Id("V")), body));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { F.Id(name), F.Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i != 0) items.Add(F.Comma);
            items.Add(arguments[i]);
        }
        items.Add(F.Close);
        return F.Seq([.. items]);
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Parenthesized(Formula formula) => F.Seq(F.Open, formula, F.Close);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
