using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class HoneycombFirstTouchDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/CellularAutomata/HoneycombFirstTouch";
    private static readonly Formula Naturals = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Integers = Seq(Mathbb, Grp(F.Id("Z")));
    private static readonly Formula Vertex = Name("Vertex");
    private static readonly Formula Vertices = CallNamed("Finset", Vertex);
    private static readonly Formula Bool = Name("Bool");
    private static readonly Formula Prop = Name("Prop");
    private static readonly Formula TouchData = CallNamed("Option", Par(Seq(Naturals, Sp, Times, Sp, Naturals)));
    private static readonly Formula Graph = F.Id("G");
    private static readonly Formula Dmn = F.Id("D");
    private static readonly Formula Outer = F.Id("E");
    private static readonly Formula Seed = F.Id("seed");
    private static readonly Formula Origin = CallNamed("A", Num(0), Num(0));

    private static readonly Formula Multiplicity = F.Id("mult");
    private static readonly Formula OtherMultiplicity = F.Id("other");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Synchronous first-touch dynamics and strict horizons in clipped honeycomb domains.",
        H("First touch in clipped honeycomb domains"),
        Blocks(
            Paragraph(Text("A stored pair gives the tick and multiplicity of the first touch. "
                + "A vertex with multiplicity one is born and sends on the next tick. "
                + "The seed starts with the pair (0, 1). In the formulas, u is the universe "
                + "of the vertex type. The witnesses e and d are Lean's typeclass arguments "
                + "for decidable equality and adjacency. A type after a colon gives "
                + "the type of a variable or of the displayed value.")),
            Definition("sending-neighbors", "sendingNeighbors", "Sending neighbors", SendingNeighbors()),
            Definition("state", "state", "Stored first-touch state", State()),
            Definition("touch", "Touch", "First touch", EventDefinitions("Touch",
                Equal(Stored(Dmn, Seed, F.Id("t"), F.Id("v")), Some(F.Id("t"), Multiplicity)), Prop, true)),
            Definition("born", "Born", "Birth", EventDefinitions("Born",
                TouchAt(Dmn, Seed, F.Id("t"), F.Id("v"), Num(1)), Prop)),
            Definition("intact", "Intact", "Intact status", EventDefinitions("Intact",
                Equal(Stored(Dmn, Seed, F.Id("t"), F.Id("v")), Name("none")), Prop)),
            Definition("senders", "senders", "Senders at a vertex", EventDefinitions("senders",
                SendersFrom(Dmn, F.Id("t"), CallNamed("state", Graph, Dmn, Seed, F.Id("t")), F.Id("v")),
                CallNamed("Finset", F.Id("V")))),
            Theorem("mem-senders", "mem_senders", "Membership in the sender set", MemSenders()),
            Theorem("touch-zero-iff", "touch_zero_iff", "First touch at tick zero", TouchZero()),
            Theorem("touch-retained-and-positive", "touch_retained_and_positive",
                "Retention and positive multiplicity", TouchRetained()),
            Theorem("intact-iff-no-touch", "intact_iff_no_touch", "Intact status through a tick", IntactIff()),
            Theorem("touch-unique", "touch_unique", "Uniqueness of touch data", TouchUnique()),
            Theorem("strict-horizon", "strict_horizon", "Strict horizon on a general graph", StrictHorizon()),
            Paragraph(Text("For honeycomb geometry, Vertex is Bool × ℤ × ℤ. Write v=(p,x,y) "
                + "and use p(v), x(v), y(v) for its projections. The operation land is "
                + "Nat.land, the bitwise AND of natural numbers. Subtraction in natural "
                + "parameters is truncated.")),
            Definition("vertex-a", "A", "A vertex", ColoredVertex("A", "false")),
            Definition("vertex-b", "B", "B vertex", ColoredVertex("B", "true")),
            Definition("neighbor-laws", "NeighborLaws", "Adjacency laws", NeighborLaws()),
            Theorem("neighbors-a", "neighbors_A", "Neighbors of an A vertex", Neighbors("A", "B", false)),
            Theorem("neighbors-b", "neighbors_B", "Neighbors of a B vertex", Neighbors("B", "A", true)),
            Definition("part", "part", "Integer color", VertexReadout("part", Integers,
                Ite(Color(F.Id("v")), Num(1), Num(0)))),
            Definition("height-sum", "heightSum", "Coordinate sum", VertexReadout("heightSum", Integers,
                Add(X(F.Id("v")), Y(F.Id("v"))))),
            Definition("g", "g", "Cut coordinate", VertexReadout("g", Integers,
                Add(Add(Multiply(Num(2), X(F.Id("v"))), Y(F.Id("v"))), Part(F.Id("v"))))),
            Definition("earliest", "earliest", "Earliest possible touch", VertexReadout("earliest", Naturals,
                ToNat(Add(G(F.Id("v")), Y(F.Id("v")))))),
            Definition("horizon", "horizon", "Displaced-wall horizon", Horizon()),
            Definition("domain", "domain", "Retained finite domain", DomainDefinition()),
            Theorem("mem-domain", "mem_domain", "Retained vertex criterion", MemDomain()),
            Theorem("domain-mono", "domain_mono", "Monotonicity in height", DomainMono()),
            Theorem("seed-mem", "seed_mem", "Seed retention", SeedMem()),
            Theorem("earliest-bound", "earliest_bound", "Lower bound on touch time", EarliestBound()),
            Definition("earliest-births", "EarliestBirths", "Sufficient parity condition", EarliestBirths()),
            Paragraph(Text("At a dyadic width dividing the smaller height, a crossing edge "
                + "can leave the smaller domain only at the diagonal A wall. Below the "
                + "dyadic width, the two eligible parents send together. At or above "
                + "that width, the earliest-touch bound suffices. Induction on time "
                + "transports the full touch data and excludes earlier exterior births.")),
            Theorem("clipped-first-touch", "clipped_first_touch", "Strict horizon across clipped honeycombs",
                ClippedFirstTouch()),
            Definition("omega-domain", "omegaDomain", "Adjacent-cut domain", OmegaDefinition()),
            Theorem("domain-cut-mono", "domain_cut_mono", "Monotonicity in the cut threshold", DomainCutMono()),
            Definition("earliest-birth-iff", "EarliestBirthIff", "Earliest-birth parity law", EarliestBirthIff()),
            Theorem("earliest-birth-iff-of-neighbor-laws", "earliestBirthIff_of_neighborLaws",
                "Parity law from the adjacency laws", OnHoneycombGraph(
                    Imp(Laws(), CallNamed("EarliestBirthIff", Graph)), decidable: true)),
            Definition("repository-adjacency", "repositoryAdjacency", "Decidable repository adjacency",
                Typed(Name("repositoryAdjacency"), DecidableAdj(Name("honeycombGraph")))),
            Theorem("repository-neighbor-laws", "repositoryNeighborLaws",
                "Adjacency laws on the repository graph", CallNamed("NeighborLaws", Name("honeycombGraph"))))));

    private static DocumentBlock Definition(string id, string name, string title, Formula statement) =>
        Mirror(id, name, title, statement, DescribeRole.Definition);

    private static DocumentBlock Theorem(string id, string name, string title, Formula statement) =>
        Mirror(id, name, title, statement, DescribeRole.Theorem);

    private static DocumentBlock Mirror(string id, string name, string title, Formula statement, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(), role);

    private static Formula SendingNeighbors()
    {
        var v = F.Id("v");
        var w = F.Id("w");
        var t = F.Id("t");
        var prior = Name("prior");
        var type = F.Id("V");
        var right = SetOf("w", type, And(Member(w, Dmn), Adj(v, w), Equal(App(prior, w), Some(t, Num(1)))));
        return OnGenericGraph(TypedEquation(SendersFrom(Dmn, t, prior, v), CallNamed("Finset", type), right),
            ("D", CallNamed("Finset", type)), ("t", Naturals), ("prior", Arrow(type, TouchData)), ("v", type));
    }

    private static Formula State()
    {
        var t = F.Id("t");
        var v = F.Id("v");
        var previous = Stored(Dmn, Seed, t, v);
        var current = Stored(Dmn, Seed, Add(t, Num(1)), v);
        var count = CallNamed("card", SendersFrom(Dmn, t, CallNamed("state", Graph, Dmn, Seed, t), v));
        var type = F.Id("V");
        var signature = Typed(CallNamed("state", Graph, Dmn, Seed), Arrow(Naturals, Arrow(type, TouchData)));
        var initial = All(Equal(Stored(Dmn, Seed, Num(0), v),
            Ite(And(Member(v, Dmn), Equal(v, Seed)), Some(Num(0), Num(1)), Name("none"))), ("v", type));
        var fresh = And(Member(v, Dmn), NotEqual(count, Num(0)));
        var next = Ite(NotEqual(previous, Name("none")), previous,
            Ite(fresh, Some(Add(t, Num(1)), count), Name("none")));
        return OnGenericGraph(And(signature, initial, All(Equal(current, next), ("t", Naturals), ("v", type))),
            ("D", CallNamed("Finset", type)), ("seed", type));
    }

    private static Formula EventDefinitions(string name, Formula right, Formula resultType, bool multiplicity = false)
    {
        var type = F.Id("V");
        var t = F.Id("t");
        var v = F.Id("v");
        var left = multiplicity ? TouchAt(Dmn, Seed, t, v, Multiplicity) : CallNamed(name, Graph, Dmn, Seed, t, v);
        var equation = resultType == Prop ? IffForm(Typed(left, Prop), right) : TypedEquation(left, resultType, right);
        return OnGenericGraph(multiplicity ? All(equation, ("mult", Naturals)) : equation,
            ("D", CallNamed("Finset", type)), ("seed", type), ("t", Naturals), ("v", type));
    }

    private static Formula MemSenders()
    {
        var t = F.Id("t");
        var v = F.Id("v");
        var w = F.Id("w");
        return GenericEvent(IffForm(Member(w, CallNamed("senders", Graph, Dmn, Seed, t, v)),
            And(Member(w, Dmn), Adj(v, w), BornAt(Dmn, Seed, t, w))),
            ("t", Naturals), ("v", F.Id("V")), ("w", F.Id("V")));
    }

    private static Formula TouchZero()
    {
        var v = F.Id("v");
        return GenericEvent(IffForm(TouchAt(Dmn, Seed, Num(0), v, Multiplicity),
            And(Member(v, Dmn), Equal(v, Seed), Equal(Multiplicity, Num(1)))), ("v", F.Id("V")), ("mult", Naturals));
    }

    private static Formula TouchRetained()
    {
        var t = F.Id("t");
        var v = F.Id("v");
        return GenericEvent(Imp(TouchAt(Dmn, Seed, t, v, Multiplicity), And(Member(v, Dmn), Positive(Multiplicity))),
            ("t", Naturals), ("v", F.Id("V")), ("mult", Naturals));
    }

    private static Formula IntactIff()
    {
        var v = F.Id("v");
        var t = F.Id("t");
        var s = F.Id("s");
        var noTouch = All(Imp(LeqOf(s, t), All(Not(TouchAt(Dmn, Seed, s, v, Multiplicity)), ("mult", Naturals))),
            ("s", Naturals));
        return GenericEvent(IffForm(CallNamed("Intact", Graph, Dmn, Seed, t, v), noTouch),
            ("t", Naturals), ("v", F.Id("V")));
    }

    private static Formula TouchUnique()
    {
        var v = F.Id("v");
        var s = F.Id("s");
        var t = F.Id("t");
        return GenericEvent(Imp(TouchAt(Dmn, Seed, s, v, Multiplicity), TouchAt(Dmn, Seed, t, v, OtherMultiplicity),
            And(Equal(s, t), Equal(Multiplicity, OtherMultiplicity))),
            ("s", Naturals), ("t", Naturals), ("v", F.Id("V")), ("mult", Naturals), ("other", Naturals));
    }

    private static Formula StrictHorizon()
    {
        var type = F.Id("V");
        var t = F.Id("t");
        var v = F.Id("v");
        var w = F.Id("w");
        var h = F.Id("h");
        var hv = App(h, v);
        var edgeStep = All(Imp(Adj(v, w), LeqOf(hv, Add(App(h, w), Num(1)))), ("v", type), ("w", type));
        var boundary = ExistsFor("w", type, And(Member(w, Dmn), Adj(v, w)));
        var wall = All(Imp(Member(v, Outer), Not(Member(v, Dmn)), boundary,
            All(Imp(Less(t, hv), Not(BornAt(Outer, Seed, t, v))), ("t", Naturals))), ("v", type));
        return OnGenericGraph(Imp(SubsetOf(Dmn, Outer), Member(Seed, Dmn), edgeStep, wall,
                All(HorizonConclusions(type, Dmn, Outer, Seed, hv), ("t", Naturals))),
            ("D", CallNamed("Finset", type)), ("E", CallNamed("Finset", type)), ("seed", type),
            ("h", Arrow(type, Naturals)));
    }

    private static Formula HorizonConclusions(Formula type, Formula inner, Formula outer, Formula seed, Formula limit)
    {
        var v = F.Id("v");
        var t = F.Id("t");
        var agreement = All(Imp(Member(v, inner), Less(t, limit), All(Imp(Positive(Multiplicity),
            IffForm(TouchAt(inner, seed, t, v, Multiplicity), TouchAt(outer, seed, t, v, Multiplicity))), ("mult", Naturals))), ("v", type));
        var noExteriorBirth = All(Imp(Member(v, outer), Not(Member(v, inner)), Less(t, limit),
            Not(BornAt(outer, seed, t, v))), ("v", type));
        return And(agreement, noExteriorBirth);
    }

    private static Formula ColoredVertex(string name, string color)
    {
        var x = F.Id("x");
        var y = F.Id("y");
        return All(TypedEquation(CallNamed(name, x, y), Vertex, Pair(Name(color), Pair(x, y))),
            ("x", Integers), ("y", Integers));
    }

    private static Formula NeighborLaws()
    {
        var v = F.Id("v");
        var w = F.Id("w");
        var x = F.Id("x");
        var y = F.Id("y");
        var a = F.Id("a");
        var b = F.Id("b");
        var opposite = All(Imp(Adj(v, w), NotEqual(Color(v), Color(w))), ("v", Vertex), ("w", Vertex));
        var fromA = All(IffForm(Adj(CallNamed("A", x, y), CallNamed("B", a, b)),
            Or(And(Equal(x, a), Equal(y, b)), And(Equal(x, Add(a, Num(1))), Equal(y, b)),
                And(Equal(x, a), Equal(y, Add(b, Num(1)))))),
            ("x", Integers), ("y", Integers), ("a", Integers), ("b", Integers));
        return OnHoneycombGraph(IffForm(Typed(Laws(), Prop), And(opposite, fromA)));
    }

    private static Formula Neighbors(string source, string target, bool increment)
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var w = F.Id("w");
        Formula Shift(Formula c) => increment ? Add(c, Num(1)) : Subtract(c, Num(1));
        return OnHoneycombGraph(Imp(Laws(), All(IffForm(Adj(CallNamed(source, x, y), w),
            Or(Equal(w, CallNamed(target, x, y)), Equal(w, CallNamed(target, Shift(x), y)),
                Equal(w, CallNamed(target, x, Shift(y))))), ("x", Integers), ("y", Integers), ("w", Vertex))));
    }

    private static Formula Horizon()
    {
        var v = F.Id("v");
        var p = F.Id("P");
        var height = Add(Add(Multiply(Num(2), X(v)), Part(v)), Multiply(Num(2), CastInt(p)));
        return All(TypedEquation(CallNamed("horizon", p, v), Naturals, ToNat(height)),
            ("P", Naturals), ("v", Vertex));
    }

    private static Formula DomainDefinition()
    {
        var a = F.Id("a");
        var k = F.Id("K");
        var v = F.Id("v");
        var interval = CallNamed("Ico", CastInt(Num(0)), CastInt(a));
        var square = Seq(CallNamed("univ", Bool), Sp, Times, Sp, Par(Seq(interval, Sp, Times, Sp, interval)));
        var filtered = Seq(OpenBrace, v, Sp, InMacro, Sp, square, Sp, Mid, Sp, DomainCuts(v, a, k), CloseBrace);
        return All(TypedEquation(Domain(a, k), Vertices, filtered), ("a", Naturals), ("K", Naturals));
    }

    private static Formula MemDomain()
    {
        var a = F.Id("a");
        var k = F.Id("K");
        var v = F.Id("v");
        return All(IffForm(Member(v, Domain(a, k)),
            And(LeqOf(Num(0), X(v)), LeqOf(Num(0), Y(v)), DomainCuts(v, a, k))),
            ("a", Naturals), ("K", Naturals), ("v", Vertex));
    }

    private static Formula DomainMono()
    {
        var m = F.Id("m");
        var n = F.Id("N");
        var k = F.Id("K");
        return All(Imp(LeqOf(m, n), SubsetOf(Domain(m, k), Domain(n, k))),
            ("m", Naturals), ("N", Naturals), ("K", Naturals));
    }

    private static Formula SeedMem()
    {
        var a = F.Id("a");
        var k = F.Id("K");
        return All(Imp(Positive(a), Positive(k), Member(Origin, Domain(a, k))), ("a", Naturals), ("K", Naturals));
    }

    private static Formula EarliestBound()
    {
        var t = F.Id("t");
        var v = F.Id("v");
        return OnHoneycombGraph(Imp(Laws(), All(Imp(TouchAt(Dmn, Origin, t, v, Multiplicity), LeqOf(Earliest(v), t)),
            ("D", Vertices), ("t", Naturals), ("mult", Naturals), ("v", Vertex))), decidable: true);
    }

    private static Formula EarliestBirths()
    {
        var v = F.Id("v");
        var right = All(Imp(Member(v, Dmn), NoSharedBit(v), BornAt(Dmn, Origin, Earliest(v), v)), ("v", Vertex));
        return OnHoneycombGraph(All(IffForm(Typed(CallNamed("EarliestBirths", Graph, Dmn), Prop), right),
            ("D", Vertices)), decidable: true);
    }

    private static Formula ClippedFirstTouch()
    {
        var m = F.Id("m");
        var n = F.Id("N");
        var k = F.Id("K");
        var p = new Formula.Power(Num(2), F.Id("b"));
        var inner = Domain(m, k);
        var outer = Domain(n, k);
        var comparisons = HorizonConclusions(Vertex, inner, outer, Origin, CallNamed("horizon", p, F.Id("v")));
        var result = Imp(Positive(m), Less(m, n), LeqOf(Num(1), k), LeqOf(k, Multiply(Num(2), m)),
            new Formula.Relation(p, FormulaRelationOperator.Divides, m), CallNamed("EarliestBirths", Graph, outer),
            All(comparisons, ("t", Naturals)));
        return OnHoneycombGraph(Imp(Laws(), All(result, ("b", Naturals), ("m", Naturals), ("N", Naturals),
            ("K", Naturals))), decidable: true);
    }

    private static Formula OmegaDefinition()
    {
        var a = F.Id("a");
        var d = F.Id("d");
        return All(TypedEquation(OmegaDomain(a, d), Vertices, Domain(a, Subtract(Multiply(Num(2), a), d))),
            ("a", Naturals), ("d", Naturals));
    }

    private static Formula DomainCutMono()
    {
        var a = F.Id("a");
        var k = F.Id("K");
        var upper = F.Id("L");
        return All(Imp(LeqOf(k, upper), SubsetOf(Domain(a, k), Domain(a, upper))),
            ("a", Naturals), ("K", Naturals), ("L", Naturals));
    }

    private static Formula EarliestBirthIff()
    {
        var a = F.Id("a");
        var d = F.Id("c");
        var v = F.Id("v");
        var cut = OmegaDomain(a, d);
        var right = All(Imp(Positive(a), LeqOf(d, a),
            All(Imp(Member(v, cut), IffForm(BornAt(cut, Origin, Earliest(v), v), NoSharedBit(v))), ("v", Vertex))),
            ("a", Naturals), ("c", Naturals));
        return OnHoneycombGraph(IffForm(Typed(CallNamed("EarliestBirthIff", Graph), Prop), right), decidable: true);
    }

    private static Formula GenericEvent(Formula body, params (string, Formula)[] parameters) =>
        OnGenericGraph(body, [("D", CallNamed("Finset", F.Id("V"))), ("seed", F.Id("V")), .. parameters]);

    private static Formula OnGenericGraph(Formula body, params (string, Formula)[] parameters) =>
        All(All(body, parameters), ("V", Seq(Name("Type"), Sp, F.Id("u"))),
            ("e", CallNamed("DecidableEq", F.Id("V"))), ("G", CallNamed("SimpleGraph", F.Id("V"))),
            ("d", DecidableAdj(Graph)));

    private static Formula OnHoneycombGraph(Formula body, bool decidable = false) =>
        All(decidable ? All(body, ("d", DecidableAdj(Graph))) : body, ("G", CallNamed("SimpleGraph", Vertex)));

    private static Formula VertexReadout(string name, Formula type, Formula right) =>
        All(TypedEquation(CallNamed(name, F.Id("v")), type, right), ("v", Vertex));

    private static Formula SendersFrom(Formula domain, Formula t, Formula prior, Formula v) =>
        CallNamed("sendingNeighbors", Graph, domain, t, prior, v);
    private static Formula Stored(Formula domain, Formula seed, Formula t, Formula v) =>
        CallNamed("state", Graph, domain, seed, t, v);
    private static Formula TouchAt(Formula domain, Formula seed, Formula t, Formula v, Formula multiplicity) =>
        CallNamed("Touch", Graph, domain, seed, t, v, multiplicity);
    private static Formula BornAt(Formula domain, Formula seed, Formula t, Formula v) =>
        CallNamed("Born", Graph, domain, seed, t, v);

    private static Formula Adj(Formula v, Formula w) => App(Adjacency(Graph), v, w);
    private static Formula Adjacency(Formula graph) => Seq(graph, Dot, Name("Adj"));
    private static Formula DecidableAdj(Formula graph) => CallNamed("DecidableRel", Adjacency(graph));
    private static Formula Laws() => CallNamed("NeighborLaws", Graph);
    private static Formula Domain(Formula a, Formula k) => CallNamed("domain", a, k);
    private static Formula OmegaDomain(Formula a, Formula d) => CallNamed("omegaDomain", a, d);
    private static Formula DomainCuts(Formula v, Formula a, Formula k) =>
        And(Less(CallNamed("heightSum", v), CastInt(a)), Less(G(v), CastInt(k)));
    private static Formula NoSharedBit(Formula v) =>
        Equal(CallNamed("land", ToNat(X(v)), ToNat(Y(v))), Num(0));
    private static Formula G(Formula v) => CallNamed("g", v);
    private static Formula X(Formula v) => CallNamed("x", v);
    private static Formula Y(Formula v) => CallNamed("y", v);
    private static Formula Color(Formula v) => CallNamed("p", v);
    private static Formula Part(Formula v) => CallNamed("part", v);
    private static Formula Earliest(Formula v) => CallNamed("earliest", v);
    private static Formula ToNat(Formula value) => App(Seq(Operatorname, Grp(F.Id("Int"), Dot, F.Id("toNat"))), value);
    private static Formula CastInt(Formula value) => Par(Typed(value, Integers));

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula CallNamed(string name, params Formula[] arguments) => App(Name(name), arguments);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula left, Formula right) => Par(Seq(left, Comma, Sp, right));
    private static Formula Some(Formula time, Formula count) => CallNamed("some", Pair(time, count));
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula TypedEquation(Formula left, Formula type, Formula right) => Equal(Par(Typed(left, type)), right);
    private static Formula Arrow(Formula domain, Formula codomain) => Seq(domain, Sp, To, Sp, codomain);
    private static Formula Ite(Formula condition, Formula yes, Formula no) => CallNamed("ite", condition, yes, no);
    private static Formula SetOf(string name, Formula type, Formula condition) =>
        Seq(OpenBrace, Typed(F.Id(name), type), Sp, Mid, Sp, condition, CloseBrace);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LeqOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);
    private static Formula Positive(Formula n) => Less(Num(0), n);
    private static Formula Not(Formula value) => Seq(Neg, Sp, Par(value));
    private static Formula IffForm(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Iff, Par(right));
    private static Formula Imp(params Formula[] clauses) => Join(FormulaLogicOperator.Implies, clauses);
    private static Formula And(params Formula[] clauses) => Join(FormulaLogicOperator.And, clauses);
    private static Formula Or(params Formula[] clauses) => Join(FormulaLogicOperator.Or, clauses);
    private static Formula Join(FormulaLogicOperator relation, Formula[] clauses)
    {
        var result = Par(clauses[^1]);
        for (var i = clauses.Length - 2; 0 <= i; i--)
            result = new Formula.Logic(Par(clauses[i]), relation, result);
        return result;
    }

    private static Formula All(Formula body, params (string Name, Formula Type)[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(variable => Bound(variable.Name, variable.Type))], body);

    private static Formula ExistsFor(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [Bound(name, type)], body);

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
}
