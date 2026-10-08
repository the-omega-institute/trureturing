using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class NestedPressureLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/NestedPressureLimit.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] p)
    {
        var r = p[^1];
        for (var k = p.Length - 2; k >= 0; --k) r = new Formula.Logic(p[k], FormulaLogicOperator.And, r);
        return r;
    }
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Config => Fn(I("Int"), I("CuLetter"));
    private static Formula Language => Call("Set", Config);
    private static Formula Word => Call("List", I("CuLetter"));
    private static Formula Lam(string n, Formula t, Formula p) => Seq(Open, I(n), Sp, Colon, Sp, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Apply(Formula f, params Formula[] a) => Call("apply", [f, ..a]);
    private static Formula Member(Formula x, Formula s) => Call("member", x, s);
    private static Formula LeqOf(Formula a, Formula b) => Call("le", a, b);
    private static Formula LtOf(Formula a, Formula b) => Call("lt", a, b);
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Div(Formula a, Formula b) => Call("divide", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);
    private static Formula Negate(Formula a) => Call("negate", a);
    private static Formula Y(Formula j) => Apply(I("Y"), j);
    private static Formula Intersection => Call("iInter", I("Y"));
    private static Formula Occupied(Formula x) => Call("Nonempty", x);
    private static Formula OccursIn(Formula x, Formula w) => Ex(And(Member(I("omega"), x), Call("Occurs", I("omega"), w)), B("omega", Config));
    private static Formula Shifted => Lam("i", I("Int"), Apply(I("omega"), Add(I("i"), I("a"))));
    private static Formula Shift(Formula x) => All(Imp(Member(I("omega"), x),
        All(Member(Shifted, x), B("a", I("Int")))), B("omega", Config));
    private static Formula CompactFamily => All(Call("IsCompact", Y(I("j"))), B("j", Nat));
    private static Formula OccupiedFamily => All(Occupied(Y(I("j"))), B("j", Nat));
    private static Formula ShiftFamily => All(Shift(Y(I("j"))), B("j", Nat));
    private static Formula Nested => Call("Antitone", I("Y"));
    private static Formula Family(Formula p, bool occupied = false) => All(Imp(
        occupied ? And(CompactFamily, OccupiedFamily, Nested, ShiftFamily) : And(CompactFamily, Nested, ShiftFamily), p),
        B("Y", Fn(Nat, Language)));
    private static Formula P(Formula x, Formula t) => Call("pressure", x, t);
    private static Formula Rate(Formula x) => Call("weightedFactorRate", x);
    private static Formula Limit(Formula f, Formula x) => Call("Tendsto", f, I("atTop"), Call("nhds", x));
    private static Formula Cylinder(Formula w) => Call("anchoredCylinder", w);
    private static Formula Memory(Formula side, Formula n, Formula d) => Call("MemoryLanguage", side, n, I("K"), d);
    private static Formula Upper(Formula n) => Memory(I("upper"), n, I("d"));
    private static Formula Auxiliary => Call("AuxiliaryLanguage", I("K"), I("d"));
    private static Formula BudgetD => Div(Div(Sub(I("lam"), I("b")), Pow(I("g"), D(2))), Pow(I("chi"), I("K")));
    private static Formula Eta => Call("etaB", I("K"), I("b"));
    private static Formula Root(Formula side, Formula n) => Apply(I("roots"), side, n);
    private static Formula GammaOf(Formula side, Formula n) => Negate(Call("logb", D(2), Root(side, n)));
    private static Formula RootProperties => All(Imp(LeqOf(I("K"), I("n")), And(
        LtOf(D(0), Root(I("side"), I("n"))), LtOf(Root(I("side"), I("n")), D(1)),
        Equal(Call("weightedRadius", I("side"), I("n"), I("K"), BudgetD, Root(I("side"), I("n"))), D(1)),
        Equal(Rate(Memory(I("side"), I("n"), BudgetD)), GammaOf(I("side"), I("n"))))),
        B("side", I("MemorySide")), B("n", Nat));
    private static Formula Budget => And(LeqOf(D(2), I("K")),
        LtOf(Sub(I("lam"), Mul(Mul(Pow(I("g"), D(2)), Pow(I("chi"), I("K"))), Call("hSide", I("high")))), I("b")),
        LtOf(I("b"), Sub(I("lam"), Mul(Mul(Pow(I("g"), D(2)), Pow(I("chi"), I("K"))),
            Div(Call("aSide", I("high")), Sub(D(1), Mul(I("rho"), Pow(I("chi"), I("K")))))))));
    private static DocumentBlock Node(string name, Formula statement, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("fib-nested-pressure-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace('_', ' ')), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact decreasing bilateral languages stabilize at every fixed word length; their pressures and weighted zeros converge to those of the actual intersection.",
        H("Nested bilateral languages and the original upper limit"), Blocks(
        Paragraph(Text("Configurations are functions from the integers to the two letters u and c, with literal weights six and twenty. Occurs is the original occurrence relation at an arbitrary integer position. The pressure and weighted factor rate are those of the actual occurring words. For the memory instance, the windows are indexed from the most recent past letter, while memoryValue evaluates the reversed chronological word; the current Kth-c guard uses the prestate before the current letter. The upper guard retains equality.")),
        Node("anchoredCylinder", All(Equal(Cylinder(I("w")), Call("setOf", Lam("omega", Config,
            All(Equal(Apply(I("omega"), Call("toInt", Call("val", I("k")))),
                Call("getElem", I("w"), Call("val", I("k")))), B("k", Call("Fin", Call("length", I("w")))))))), B("w", Word)),
            "The cylinder fixes every letter of w at coordinates zero through length w minus one. The empty word gives the entire configuration space.", DescribeRole.Definition),
        Node("persistent_word_intersection", Family(All(Imp(All(OccursIn(Y(I("j")), I("w")), B("j", Nat)),
            Ex(And(Member(I("omega"), Intersection), Member(I("omega"), Cylinder(I("w")))), B("omega", Config))), B("w", Word))),
            "Translate each occurrence to zero using shift invariance. The intersections of the compact languages with this closed cylinder form nonempty nested compact closed sets. Their common point realizes w in the actual intersection even when the original occurrence positions vary arbitrarily."),
        Node("nested_language_stabilization", Family(All(Ex(All(Imp(LeqOf(I("J"), I("j")),
            All(Imp(Equal(Call("length", I("w")), I("k")), Equivalent(OccursIn(Y(I("j")), I("w")), OccursIn(Intersection, I("w")))),
                B("w", Word))), B("j", Nat)), B("J", Nat)), B("k", Nat))),
            "A word either persists and has a common realization, or disappears permanently. Finitely many binary words of one fixed length give one common eventual index. This proves equality of the actual word languages at every fixed length, including zero."),
        Node("pressure_mono", All(Imp(And(Occupied(I("X")), Occupied(I("Z")), Call("subset", I("X"), I("Z"))),
            LeqOf(P(I("X"), I("theta")), P(I("Z"), I("theta")))), B("X", Language), B("Z", Language), B("theta", Real)),
            "The inclusion injects the actual finite dictionaries, preserving every positive monomial. Passing their logarithmic quotients to the pressure limit gives the comparison for every real exponent."),
        Node("nested_pressure_limit", Family(All(And(Occupied(Intersection),
            Call("Antitone", Lam("j", Nat, P(Y(I("j")), I("theta")))),
            Equal(Call("iInf", Lam("j", Nat, P(Y(I("j")), I("theta")))), P(Intersection, I("theta"))),
            Limit(Lam("j", Nat, P(Y(I("j")), I("theta"))), P(Intersection, I("theta")))), B("theta", Real)), true),
            "For every real theta, minus twenty times its absolute value bounds all positive-length logarithmic quotients uniformly in the language index and length. This bounds both product index orders and permits the two infima to commute. Stabilization identifies each fixed-length infimum with the intersection partition sum, so the pressures decrease to the exact intersection pressure."),
        Node("nested_rate_limit", Family(And(Call("Antitone", Lam("j", Nat, Rate(Y(I("j"))))),
            Limit(Lam("j", Nat, Rate(Y(I("j")))), Rate(Intersection))), true),
            "Inclusion bounds each zero below by the intersection zero. At that zero plus any positive a, the literal upper pressure slope gives pressure at most minus six a. Pressure convergence makes the approximating pressure negative there, which bounds its zero above. No positive-entropy hypothesis is needed."),
        Node("upper_memory_subshift", All(Imp(LeqOf(D(1), I("K")), And(Occupied(Upper(I("n"))),
            Call("IsClosed", Upper(I("n"))), Call("IsCompact", Upper(I("n"))), Shift(Upper(I("n"))))),
            B("n", Nat), B("K", Nat), B("d", Real)),
            "The all-u configuration satisfies the finite constraints. Each run condition is clopen, and window_value expresses the guard as a continuous finite-window value with a weak lower inequality. The complete constraints are closed, hence compact in the bilateral finite-letter product. Translating the constraints proves shift invariance, including at n equal to K."),
        Node("original_upper_rate_limit", All(Imp(LeqOf(D(1), I("K")), And(
            Call("Antitone", Lam("n", Nat, Rate(Upper(I("n"))))),
            Limit(Lam("n", Nat, Rate(Upper(I("n")))), Rate(Auxiliary)))), B("K", Nat), B("d", Real)),
            "Apply the nested result to Y j equal to MemoryLanguage upper (K+j) K d. The original upper-memory intersection is exactly AuxiliaryLanguage K d. Removing the finite initial segment gives the upper rate limit along every n at least K."),
        Node("original_upper_root_limit", All(Imp(Budget, Ex(And(RootProperties,
            All(Imp(LeqOf(I("K"), I("n")), And(LeqOf(GammaOf(I("lower"), I("n")), Eta),
                LeqOf(Eta, GammaOf(I("upper"), I("n"))))), B("n", Nat)),
            Call("MonotoneOn", Lam("n", Nat, GammaOf(I("lower"), I("n"))), Call("Ici", I("K"))),
            Call("AntitoneOn", Lam("n", Nat, GammaOf(I("upper"), I("n"))), Call("Ici", I("K"))),
            Limit(Lam("n", Nat, GammaOf(I("upper"), I("n"))), Eta),
            All(Equal(Call("actualRate", I("model"), I("K"), BudgetD, I("strict")), Eta),
                B("model", I("Model")), B("strict", I("Bool")))), B("roots", Fn(I("MemorySide"), Fn(Nat, Real))))),
            B("o", I("Ownership")), B("b", Real), B("K", Nat)),
            "Under both original source-budget inequalities and K at least two, the exact spectral root families retain their radius-one equations, rate identities, sandwich and monotonicity on n at least K. Their upper logarithmic rates converge downward to the same eta_b supplied by the actual count bridge. This eta_b is also the actual rate for each source model and each strict or weak guard flag. The conclusion holds for every ownership assignment."))));
}
