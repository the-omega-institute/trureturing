using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CycleStarIrregularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/salmanageshnarahari2024cyclestar");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cycle-star edge irregularity strength attains both conjectured sharp bounds.",
        H("Edge irregularity strength of cycle-star graphs"),
        Blocks(
            Node("IsKLabeling", "Vertex labels between one and K", KLabelingFormula(),
                "Section 1, printed page 726: “A vertex labeling φ:V(G) → {1, 2,…,k} is called k-labeling.” "
                + "Here K is the label bound and V is the vertex type. Every vertex receives a natural "
                + "number between one and K; vertex labels may repeat.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("edgeWeight", "An edge weight is its endpoint sum", EdgeWeightFormula(),
                "Section 1, printed page 726: “The weight of an edge uv in G, written wφ(uv), is the sum "
                + "of the labels of end vertices u and v, i.e., wφ(uv)=φ(u)+φ(v).” "
                + "The function f below is the source's phi.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsEdgeIrregularLabeling", "Different unordered edges have different weights", IrregularFormula(),
                "Section 1, printed page 726: “A vertex k-labeling of a graph G is defined to be an edge "
                + "irregular k-labeling of the graph G if for every two different edges u and v, wφ(u) ≠ wφ(v).” "
                + "Equality of weights therefore implies equality in Sym2. The notation s(u,v) denotes "
                + "the unordered pair, so reversing an edge preserves it.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsEdgeIrregularityStrength", "Attainment and least positive bound", StrengthFormula(),
                "Section 1, printed page 726: “The minimum k for which the graph G has an edge irregular "
                + "k-labeling is called the edge irregularity strength of G, written es(G).” "
                + "IsLeast requires a labeling at K and comparison with every positive feasible L.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cycleStar", "The source's cycle with leaves at one vertex", CycleStarFormula(),
                "Section 1, printed page 727: “The cycle-star graph, written CSₖ,ₙ₋ₖ, is a graph with n "
                + "vertices consisting of the cycle graph of length k and n-k leafs appended to the same "
                + "vertex of the cycle.” The source gives V(CSₖ,ₙ₋ₖ)={v,vᵢ: 1 ≤ i ≤ n-1} and "
                + "E(CSₖ,ₙ₋ₖ)={vvᵢ:1≤i≤n-k} ∪ {vvₙ₋ₖ₊₁,vvₙ₋₁} ∪ {vᵢvᵢ₊₁:n-k+1≤i≤n-2}. "
                + "Fin n has n vertices: zero is v and positive i is vᵢ. SimpleGraph.fromRel adds reverse "
                + "orientations and removes loops. The value function val reads a Fin index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 3.1 with both parameter ranges", EquivFormula(F.Id("claim"), ClaimBody()),
                "Conjecture 3.1, end of Section 3, printed page 738: “Let G=CSₖ,ₙ₋ₖ be a cycle-star graph. "
                + "For k ≥ 8 and n-k ≥ 1,” followed by “es(G):= ⌈(n+1)/2⌉ for k+1 ≤ n ≤ 2k-4; "
                + "n-k+2 for n ≥ 2k-3.” All parameters are natural numbers. Nat.div is integer division, "
                + "and Nat.div(n+2,2) equals the source ceiling. Natural subtraction is truncated. Both "
                + "implications retain their full source ranges and the common hypotheses.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Both conjectured bounds are attained and minimal", ClaimBody(),
                "Put m=n-k and K=max(m+2,Nat.div(m+k+2,2)). An edge irregular labeling needs at least "
                + "m+2 distinct labels among the common vertex's neighbors. Its m+k distinct edge sums "
                + "belong to the interval from 2 through 2L, giving m+k<=2L-1 for any feasible bound L. "
                + "For the upper bound, label the common vertex K. The internal path labels start with "
                + "Nat.div(j+1,2). When K<=k-2, increase exactly those terms with j>K and j-K odd. "
                + "Consecutive sums are j+1 below the threshold and j+2 above it. Thus the first closing "
                + "edge uses the omitted sum K+1. The second closing sum exceeds all internal sums. "
                + "Fin.succAbove chooses leaf labels while skipping the other endpoint label; all their "
                + "sums lie in the remaining upper interval and are distinct. When K>=k-1, all internal "
                + "sums are at most K, and the closing and leaf sums are larger. The resulting labeling "
                + "attains K, and the two lower bounds prove leastness. Splitting at n=2k-3 gives exactly "
                + "the displayed assertion.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("cycle-star-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat => F.Id("Nat");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Name(string value) => Seq(Operatorname, Grp(F.Id(value)));
    private static Formula Qualified(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Name(name), arguments);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula EquivFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Fn(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Pair(Formula u, Formula v) => Seq(F.Id("s"), Parenthesized(Seq(u, Comma, v)));

    private static Formula KLabelingFormula()
    {
        var v = F.Id("V"); var k = F.Id("K"); var f = F.Id("f"); var x = F.Id("x");
        return All("V", F.Id("Type"), All("K", Nat, All("f", Fn(v, Nat),
            EquivFormula(Call("IsKLabeling", k, f), All("x", v,
                And(Leq(D(1), App(f, x)), Leq(App(f, x), k)))))));
    }

    private static Formula EdgeWeightFormula()
    {
        var v = F.Id("V"); var f = F.Id("f"); var u = F.Id("u"); var w = F.Id("v");
        return All("V", F.Id("Type"), All("f", Fn(v, Nat), All("u", v, All("v", v,
            Eqn(Call("edgeWeight", f, u, w), Add(App(f, u), App(f, w)))))));
    }

    private static Formula IrregularFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var k = F.Id("K"); var f = F.Id("f");
        var u = F.Id("u"); var w = F.Id("v"); var x = F.Id("x"); var y = F.Id("y");
        var distinct = All("u", v, All("v", v, All("x", v, All("y", v,
            Imp(App(Qualified("SimpleGraph", "Adj"), g, u, w),
                Imp(App(Qualified("SimpleGraph", "Adj"), g, x, y),
                    Imp(Eqn(Call("edgeWeight", f, u, w), Call("edgeWeight", f, x, y)),
                        Eqn(Pair(u, w), Pair(x, y)))))))));
        return All("V", F.Id("Type"), All("G", Call("SimpleGraph", v), All("K", Nat,
            All("f", Fn(v, Nat), EquivFormula(Call("IsEdgeIrregularLabeling", g, k, f),
                And(Call("IsKLabeling", k, f), distinct))))));
    }

    private static Formula StrengthFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var k = F.Id("K"); var l = F.Id("L");
        var feasible = And(Leq(D(1), l), Some("f", Fn(v, Nat),
            Call("IsEdgeIrregularLabeling", g, l, F.Id("f"))));
        var set = Seq(OpenBrace, l, Sp, Colon, Sp, Nat, Sp, Bar, Sp, feasible, CloseBrace);
        return All("V", F.Id("Type"), All("G", Call("SimpleGraph", v), All("K", Nat,
            EquivFormula(Call("IsEdgeIrregularityStrength", g, k), Call("IsLeast", set, k)))));
    }

    private static Formula CycleStarFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var m = Sub(n, k);
        var a = Call("val", F.Id("a")); var b = Call("val", F.Id("b"));
        var hub = And(Eqn(a, D(0)), Or(And(Leq(D(1), b), Leq(b, m)),
            Or(Eqn(b, Add(m, D(1))), Eqn(b, Sub(n, D(1))))));
        var path = And(Leq(Add(m, D(1)), a), And(Leq(a, Sub(n, D(2))), Eqn(b, Add(a, D(1)))));
        var relation = Seq(F.Id("fun"), Sp,
            Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Call("Fin", n))), Sp,
            Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Call("Fin", n))), Sp, Mapsto, Sp, Or(hub, path));
        return All("k", Nat, All("n", Nat, Eqn(Call("cycleStar", k, n),
            App(Qualified("SimpleGraph", "fromRel"), Parenthesized(relation)))));
    }

    private static Formula ClaimBody()
    {
        var k = F.Id("k"); var n = F.Id("n"); var twice = Mul(D(2), k);
        var graph = Call("cycleStar", k, n);
        var first = Imp(And(Leq(Add(k, D(1)), n), Leq(n, Sub(twice, D(4)))),
            Call("IsEdgeIrregularityStrength", graph, App(Qualified("Nat", "div"), Add(n, D(2)), D(2))));
        var second = Imp(Leq(Sub(twice, D(3)), n),
            Call("IsEdgeIrregularityStrength", graph, Add(Sub(n, k), D(2))));
        return All("k", Nat, All("n", Nat, Imp(Leq(D(8), k), Imp(Leq(D(1), Sub(n, k)), And(first, second)))));
    }
}
