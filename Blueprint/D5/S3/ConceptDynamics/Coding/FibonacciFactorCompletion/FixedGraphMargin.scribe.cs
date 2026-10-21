using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class FixedGraphMarginDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedGraphMargin.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] p) { var r = p[^1]; for (var k = p.Length - 2; k >= 0; --k) r = new Formula.Logic(p[k], FormulaLogicOperator.And, r); return r; }
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Int => I("Int");
    private static Formula Returns => Call("List", I("Return"));
    private static Formula Letters => Call("List", I("CuLetter"));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Seq => Fn(Int, I("CuLetter"));
    private static Formula Ap(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);
    private static Formula Div(Formula a, Formula b) => Call("divide", a, b);
    private static Formula Min(Formula a, Formula b) => Call("min", a, b);
    private static Formula Lt(Formula a, Formula b) => Call("lt", a, b);
    private static Formula Le(Formula a, Formula b) => Call("le", a, b);
    private static Formula Member(Formula x, Formula s) => Call("member", x, s);
    private static Formula Nonempty(Formula s) => Call("Nonempty", s);
    private static Formula High => I("high");
    private static Formula H => Call("hSide", High);
    private static Formula A => Call("aSide", High);
    private static Formula Gtwo => Pow(I("g"), D(2));
    private static Formula Cpower => Pow(I("chi"), I("K"));
    private static Formula Guard => Div(Div(Sub(I("lam"), I("b")), Gtwo), Cpower);
    private static Formula Tau(Formula d) => Mul(Pow(I("chi"), Sub(I("K"), D(1))), d);
    private static Formula Values(Formula d) => Call("graphGapValues", I("n"), I("K"), d);
    private static Formula Margin(Formula d) => Call("graphMargin", I("n"), I("K"), d);
    private static Formula Floor => Call("resetFloor", I("R"));
    private static Formula ActualMargin => Call("fixedGraphActualMargin", I("n"), I("K"), I("b"), I("R"));
    private static Formula Canonical(Formula xs) => Call("CanonicalFactorCompletion", I("R"), I("w"), xs);
    private static Formula Params(Formula p) => All(p, B("n", Nat), B("K", Nat), B("d", Real));
    private static Formula Lambda(string n, Formula t, Formula body) => F.Seq(Open, I(n), Sp, Colon, Sp, t, Sp, Mapsto, Sp, body, Close);
    private static Formula GapMinimum() => Disp(Params(Imp(Nonempty(Values(I("d"))), And(
        Lt(D(0), Margin(I("d"))), Call("IsLeast", Call("toSet", Values(I("d"))), Margin(I("d")))))));
    private static Formula HighGap()
    {
        var high = All(Equal(Ap(I("omega"), Sub(I("i"), Call("toInt", I("k")))), I("c")), B("k", Call("Fin", I("K"))));
        return Disp(Params(All(Imp(And(Lt(D(0), I("K")), Le(I("K"), I("n")),
            Member(I("omega"), Call("MemoryLanguage", I("lower"), I("n"), I("K"), I("d"))), high),
            And(Nonempty(Values(I("d"))), Le(Margin(I("d")), Sub(Call("pastState", I("omega"), I("i")), Tau(I("d")))))),
            B("omega", Seq), B("i", Int))));
    }
    private static Formula Unique() => Disp(All(Imp(And(Canonical(I("xs")), Canonical(I("ys"))), Equal(I("xs"), I("ys"))),
        B("R", I("Return")), B("w", Letters), B("xs", Returns), B("ys", Returns)));
    private static Formula FullMargin()
    {
        var q = Sub(I("lam"), Mul(Mul(Gtwo, Cpower), H));
        var psi = Sub(I("lam"), Mul(Mul(Gtwo, Cpower), Div(A, Sub(D(1), Mul(I("rho"), Cpower)))));
        var above = Lt(Call("max", Call("max", Call("xSide", High), Call("ySide", High)), Guard), Floor);
        var factor = Ex(And(Member(I("omega"), Call("MemoryLanguage", I("lower"), I("n"), I("K"), Guard)),
            Call("Occurs", I("omega"), I("w"))), B("omega", Seq));
        Formula Supplied(Formula xs) => Call("ActualPairSupply", I("model"), I("o"), Sub(I("b"), ActualMargin), I("strict"), xs);
        var extra = Call("if", Member(I("c"), I("w")),
            Call("if", Equal(Call("getLastOption", I("w")), Call("some", I("c"))), D(1, 2), D(6)), D(0));
        Formula Weight(Formula xs) => Equal(Call("listWeight", xs), Add(Add(Call("wordWeight", I("w")),
            Add(D(2, 0), Mul(D(6), Call("m", I("R"))))), extra));
        Formula Product(Formula xs) => And(Canonical(xs), Supplied(xs), Weight(xs));
        var completions = All(Imp(factor, Ex(And(Product(I("xs")),
            All(Imp(Product(I("ys")), Equal(I("ys"), I("xs"))), B("ys", Returns))), B("xs", Returns))),
            B("model", I("Model")), B("o", I("Ownership")), B("w", Letters));
        var conclusion = Ex(And(Equal(Call("r", I("R")), D(1)), above, Lt(D(0), ActualMargin),
            Imp(Nonempty(Values(Guard)), And(Lt(D(0), Margin(Guard)), Call("IsLeast", Call("toSet", Values(Guard)), Margin(Guard)))),
            completions), B("R", I("Return")));
        return Disp(All(Imp(And(Le(D(2), I("K")), Le(I("K"), I("n")), Lt(q, I("b")), Lt(I("b"), psi)), conclusion),
            B("n", Nat), B("K", Nat), B("b", Real)));
    }
    private static Formula ValuesDefinition()
    {
        var vertex = Call("MemoryVertex", I("n"));
        var allowed = And(Call("MemoryEdge", I("lower"), I("K"), I("d"), I("v"), I("c"),
            Call("memoryShift", I("v"), I("c"))), Call("memoryRun", I("v"), I("c"), I("K")));
        var vertices = Call("filter", Call("univ", vertex), Lambda("v", vertex, allowed));
        var gaps = Call("image", vertices, Lambda("v", vertex, Sub(Call("memoryValue", I("v"), D(0)), Tau(I("d")))));
        return Disp(Params(Equal(Values(I("d")), gaps)));
    }
    private static Formula MarginDefinition() => Disp(Params(Equal(Margin(I("d")), Call("if", Nonempty(Values(I("d"))),
        Call("finiteMinimum", Values(I("d"))), D(0)))));
    private static Formula FloorDefinition() => Disp(All(Equal(Floor, Sub(H, Mul(Pow(I("rho"), Call("m", I("R"))),
        Sub(H, Mul(I("chi"), A))))), B("R", I("Return"))));
    private static Formula ActualDefinition()
    {
        var automatic = Sub(I("b"), Call("actualAutomaticCost", I("K")));
        var reset = Mul(Mul(Gtwo, Cpower), Sub(Floor, Guard));
        var graph = Mul(Mul(Gtwo, I("chi")), Margin(Guard));
        return Disp(All(Equal(ActualMargin, Call("if", Nonempty(Values(Guard)),
            Div(Min(Min(automatic, reset), graph), D(2)), Div(Min(automatic, reset), D(2)))),
            B("n", Nat), B("K", Nat), B("b", Real), B("R", I("Return"))));
    }
    private static Formula CanonicalDefinition()
    {
        var filled = Call("if", Equal(Call("getLastOption", I("w")), Call("some", I("c"))),
            Call("append", I("w"), Call("singleton", I("u"))), I("w"));
        var parse = Equal(filled, Call("append", Call("replicate", I("a"), I("u")),
            Call("executionWord", Call("cons", I("first"), I("rest")))));
        var reset = Call("Return", Add(Call("m", I("R")), I("a")), D(1));
        var extra = Call("Return", Add(Call("m", I("first")), D(1)), Call("r", I("first")));
        var contains = Ex(And(parse, Equal(I("xs"), Call("cons", reset, Call("cons", extra, I("rest"))))),
            B("a", Nat), B("first", I("Return")), B("rest", Returns));
        var allu = And(Equal(I("w"), Call("replicate", Call("length", I("w")), I("u"))),
            Equal(I("xs"), Call("singleton", Call("Return", Add(Call("m", I("R")), Call("length", I("w"))), D(1)))));
        return Disp(All(Equal(Canonical(I("xs")), Call("if", Member(I("c"), I("w")), contains, allu)),
            B("R", I("Return")), B("w", Letters), B("xs", Returns)));
    }
    private static DocumentBlock Node(string name, Formula statement, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("fib-fixed-graph-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
        H(name.Replace('_', ' ')), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite lower graph determines one positive error margin for every canonical actual factor completion, before any factor is chosen.",
        H("Fixed lower graphs and common actual margins"), Blocks(
        Node("graphGapValues", ValuesDefinition(), "MemoryVertex(n) is the original n-letter past, indexed from the most recent letter. graphGapValues includes every allowed high edge of the ambient lower graph, even if that edge is not retained on a bilateral path. Since an edge has target memoryShift(v,c), recording its source vertex records the entire high edge. Its gap is memoryValue(v,0)-chi^(K-1)*d. The edge's strict guard makes each gap positive. These are real comparisons defining an exact finite mathematical object; no effective decision procedure for arbitrary real budgets is asserted.", DescribeRole.Definition),
        Node("graphMargin", MarginDefinition(), "When graphGapValues is nonempty, graphMargin is its attained finite minimum. finiteMinimum denotes Finset.min' with the nonempty proof supplied by that branch. The zero in the other branch is a placeholder; it is never used as a positive graph margin.", DescribeRole.Definition),
        Node("graph_gap_minimum", GapMinimum(), "The allowed high-edge set is finite, and every lower-edge gap is strictly positive. Its attained minimum is therefore positive and is exactly epsilon_graph. IsLeast includes membership in the gap set and comparison with every other member; an arbitrary smaller bound is not substituted for the minimum.", DescribeRole.Theorem),
        Node("lower_graph_high_gap", HighGap(), "For n at least K and positive K, the unique actual memory path reconstructs the original past word. At a high letter its memoryRun is the original K-letter c-run, so its allowed lower edge contributes to graphGapValues. The zero-seed memory value is at most the bilateral state at that same position. Thus every original high guard is at least tau+epsilon_graph. In particular a graph with no allowed high edge has no high position in any of its bilateral paths.", DescribeRole.Theorem),
        Node("resetFloor", FloorDefinition(), "R=(m(R),1) is the low reset, with paid length 20+6m(R). Its floor B is attained at the auxiliary input A_H. Every actual complete initial state exceeds A_H, and the merged leading u run can only increase the reset output.", DescribeRole.Definition),
        Node("fixedGraphActualMargin", ActualDefinition(), "Here d=(lam-b)/g^2/chi^K and tau=chi^(K-1)*d. The three entries are b-C_auto, g^2*chi^K*(B-d), and g^2*chi*epsilon_graph. Taking half their minimum leaves strict room to move every nearest target into its actual color-cell interior, independently of all five ownership flags. If no allowed high edge exists, the graph term is omitted, while the positive reset term is retained as a conservative bound.", DescribeRole.Definition),
        Node("CanonicalFactorCompletion", CanonicalDefinition(), "If w contains c, fill its last return with one terminal u exactly when it ends in c. Parse its leading u run and its positive first and rest returns. Merge the leading run into the reset; add one u immediately after the first visible c-run's return, even if it is low. The construction does not move the extra u to the first high return. An all-u word, including the empty factor, merely extends the reset's u run. Return(m,r) denotes the original positive-exponent constructor. The predicate uses literal runs and no supply or margin conclusion.", DescribeRole.Definition),
        Node("canonical_factor_completion_unique", Unique(), "The unique leading-run and complete-return decomposition determines the literal completion. Uniqueness is independent of errors, scalar state choices and actual supply.", DescribeRole.Theorem),
        Node("fixed_lower_graph_actual_margin", FullMargin(), "Fix K at least two, b in the original transition interval, and n at least K. One finite low reset and one positive epsilon_actual are chosen before all factors, either actual model and every ownership assignment. Each graph factor has exactly its canonical completed list, the displayed weight overhead and strict actual errors below b-epsilon_actual. There is no bound on original or completed length, return exponent m, depth or total weight. The empty and all-u cases have overhead 20+6m(R); c-containing factors add six or twelve according to their original last letter.", DescribeRole.Theorem),
        Paragraph(Text("The reset protects only the first visible return. If that return is high, its actual input exceeds B, so its active cost is at most b-g^2*chi^K*(B-d); if low, it passes by C_auto. The extra u then makes its completed output dominate the original auxiliary output. Later high returns inherit the graph guard, including the first high return after a low first return. The invariant along their live recurrence is min(B,d+epsilon_graph/chi^(K-1)); multiplying its gap by g^2*chi^K gives exactly the minimum of the reset and graph cost gains. It does not rely on a positive infimum of per-factor strict gaps. With no allowed high edge the auxiliary guard is vacuous, so the reset-only half minimum suffices.")),
        Paragraph(Text("ActualPairSupply uses the same completed execution list on both original literal sources. It reads every departure of the stem, paid anchor when present, and all repeated blocks. Beyond the history length the error is zero, and the full future is the zero-error readout of each original literal tail. The auxiliary bilateral sequence is used only for the occurrence and its quantitative guard. It is not an actual eventually-empty source. A fixed graph's margin may shrink as n changes; this theorem does not supply a common margin over all memory graphs or identify a global decoder optimum.")))));
}
