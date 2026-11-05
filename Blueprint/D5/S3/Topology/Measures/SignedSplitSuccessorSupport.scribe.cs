using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedSplitSuccessorSupportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/SignedSplitSuccessorSupport.";
    private static Formula V(string s) => F.Id(s);
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string s, Formula type, Formula body) =>
        Seq(Exists, Sp, V(s), Colon, Sp, type, Comma, Sp, body);
    private static Formula Par(Formula a) => Seq(F.Open, a, F.Close);
    private static Formula Arr(Formula a, Formula b) => Seq(Par(a), Sp, Rightarrow, Sp, Par(b));
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Par(a), Sp, Leftrightarrow, Sp, Par(b));
    private static Formula Lam(string x, Formula body) => Grp(Seq(V(x), Sp, Mapsto, Sp, body));
    private static Formula Ev(Formula l, string x, Formula body) => Call("Eventually", l, Lam(x, body));
    private static Formula Set(Formula a) => Call("Set", a);
    private static Formula SM(Formula a) => Call("SignedMeasure", a);
    private static Formula TV(Formula a) => Call("totalVariation", a);
    private static Formula Map(Formula a, Formula b) => Call("map", a, b);
    private static Formula Compl(Formula a) => Call("compl", a);
    private static Formula Inter(Formula a, Formula b) => Call("inter", a, b);
    private static Formula SF(Formula a) => Call("toWeakDual", Call("signedFunctional", a));
    private static Formula At(string f, params Formula[] args) => Call(f, args);
    private static Formula Inst(string cls, Formula type, Formula body) =>
        Seq(OpenBracket, Call(cls, type), CloseBracket, Sp, body);
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(F.Frac, Grp(numerator), Grp(denominator));
    private static Formula CoordinateMap() => Lam("x", Lam("c", At("coord", V("c"), V("x"))));

    private static Formula UniformStatement()
    {
        var k = V("K"); var lspace = V("L"); var index = V("I"); var c = V("C");
        var n = V("n"); var x = V("x"); var y = V("y"); var p = V("p");
        var sn = At("s", n); var nun = At("nu", n); var vn = At("V", n);
        var fibre = All("x", k, All("y", k,
            Arr(Mem(At("p", x), vn), Arr(Mem(At("p", y), vn),
                Arr(Eq(At("p", x), At("p", y)),
                    Eq(At("coord", V("c"), x), At("coord", V("c"), y)))))));
        var limit = At("Tendsto", Lam("n", SF(sn)), V("l"), At("nhds", SF(V("mu"))));
        var f = CoordinateMap();
        var conclusion = All("eps", V("Real"), Arr(Lt(D(0), V("eps")), Ev(V("l"), "n",
            All("t", SM(k), Arr(Eq(Map(V("t"), p), nun),
                Arr(Eq(At("apply", TV(V("t")), V("univ")),
                    At("apply", TV(nun), V("univ"))),
                    And(Lt(At("real", TV(At("sub", Map(V("t"), f), Map(V("mu"), f))),
                            V("univ")), V("eps")),
                        Eq(Map(TV(V("t")), f), Map(TV(sn), f)))))))));
        var hypotheses = Arr(All("n", index, Eq(Map(sn, p), nun)),
            Arr(All("n", index, Eq(At("apply", TV(sn), V("univ")),
                    At("apply", TV(nun), V("univ")))),
            Arr(All("n", index, Eq(At("apply", TV(nun), Compl(vn)), D(0))),
            All("coord", Fn(c, At("ContinuousMap", k, V("Bool"))),
            Arr(All("c", c, Ev(V("l"), "n", fibre)), Arr(limit, conclusion))))));
        Formula body = hypotheses;
        body = All("mu", SM(k), body);
        body = All("s", Fn(index, SM(k)), body);
        body = All("nu", Fn(index, SM(lspace)), body);
        body = Arr(All("n", index, At("IsClopen", vn)), body);
        body = All("V", Fn(index, Set(lspace)), body);
        body = Arr(At("Continuous", p), body);
        body = All("p", Fn(k, lspace), body);
        body = Inst("Fintype", c, body);
        body = All("C", V("Type"), body);
        body = All("l", At("Filter", index), body);
        body = All("I", V("Type"), body);
        body = Inst("BorelSpace", lspace, body);
        body = Inst("MeasurableSpace", lspace, body);
        body = Inst("T2Space", lspace, body);
        body = Inst("TopologicalSpace", lspace, body);
        body = All("L", V("Type"), body);
        body = Inst("BorelSpace", k, body);
        body = Inst("MeasurableSpace", k, body);
        body = Inst("CompactSpace", k, body);
        body = Inst("TopologicalSpace", k, body);
        return Disp(All("K", V("Type"), body));
    }

    private static Formula AuxiliaryStatement()
    {
        var k = V("K"); var lspace = V("L"); var nat = V("Nat"); var c = V("C");
        var n = V("n"); var m = V("m"); var x = V("x"); var y = V("y"); var p = V("p");
        var filter = At("inf", V("atTop"), At("principal", V("S")));
        var f = CoordinateMap();
        Formula Fibre(Formula index) => All("x", k, All("y", k,
            Arr(Mem(At("p", x), At("V", index)), Arr(Mem(At("p", y), At("V", index)),
                Arr(Eq(At("p", x), At("p", y)),
                    Eq(At("coord", V("c"), x), At("coord", V("c"), y)))))));
        var candidate = All("t", SM(k), Arr(Eq(Map(V("t"), p), At("nu", m)),
            Arr(Eq(At("apply", TV(V("t")), V("univ")), At("apply", TV(At("nu", m)), V("univ"))),
            And(Lt(At("real", TV(At("sub", Map(V("t"), f), Map(V("mu"), f))), V("univ")), V("eps")),
                Eq(Map(TV(V("t")), f), Map(TV(At("s", m)), f))))));
        var result = Ex("m", nat, And(Mem(m, V("S")), And(Lt(V("M"), m),
            And(Lt(At("real", V("v"), At("preimage", p, At("V", m))), V("delta")),
                And(All("c", c, Fibre(m)), candidate)))));
        Formula body = Arr(Lt(D(0), V("eps")), Arr(Lt(D(0), V("delta")), result));
        body = All("delta", V("Real"), body);
        body = All("eps", V("Real"), body);
        body = All("M", nat, body);
        body = Arr(At("Pairwise", Lam("n", Lam("m", At("Disjoint", At("preimage", p, At("V", n)),
            At("preimage", p, At("V", m)))))), body);
        body = Inst("IsFiniteMeasure", V("v"), body);
        body = All("v", At("Measure", k), body);
        body = Arr(At("Tendsto", Lam("n", SF(At("s", n))), filter, At("nhds", SF(V("mu")))), body);
        body = Arr(All("c", c, Ev(filter, "n", Fibre(n))), body);
        body = All("coord", Fn(c, At("ContinuousMap", k, V("Bool"))), body);
        body = Arr(All("n", nat, Eq(At("apply", TV(At("nu", n)), Compl(At("V", n))), D(0))), body);
        body = Arr(All("n", nat, Eq(At("apply", TV(At("s", n)), V("univ")),
            At("apply", TV(At("nu", n)), V("univ")))), body);
        body = Arr(All("n", nat, Eq(Map(At("s", n), p), At("nu", n))), body);
        body = All("mu", SM(k), body);
        body = All("s", Fn(nat, SM(k)), body);
        body = All("nu", Fn(nat, SM(lspace)), body);
        body = Arr(All("n", nat, At("IsClopen", At("V", n))), body);
        body = All("V", Fn(nat, Set(lspace)), body);
        body = Arr(At("Continuous", p), body);
        body = All("p", Fn(k, lspace), body);
        body = Arr(At("Infinite", V("S")), body);
        body = All("S", Set(nat), body);
        body = Inst("Fintype", c, body);
        body = All("C", V("Type"), body);
        body = Inst("BorelSpace", lspace, body);
        body = Inst("MeasurableSpace", lspace, body);
        body = Inst("T2Space", lspace, body);
        body = Inst("TopologicalSpace", lspace, body);
        body = All("L", V("Type"), body);
        body = Inst("BorelSpace", k, body);
        body = Inst("MeasurableSpace", k, body);
        body = Inst("CompactSpace", k, body);
        body = Inst("TopologicalSpace", k, body);
        return Disp(All("K", V("Type"), body));
    }

    private static Formula TargetIndexStatement()
    {
        var k = V("K"); var lspace = V("L"); var nat = V("Nat"); var f = V("F");
        var n = V("n"); var j = V("j"); var x = V("x"); var y = V("y"); var p = V("p");
        var filter = At("inf", V("atTop"), At("principal", V("S")));
        var fibre = All("x", k, All("y", k, Arr(Mem(At("p", x), At("V", n)),
            Arr(Mem(At("p", y), At("V", n)), Arr(Eq(At("p", x), At("p", y)),
                Iff(Mem(x, At("A", j)), Mem(y, At("A", j))))))));
        var candidate = All("t", SM(k), Arr(Eq(Map(V("t"), p), At("nu", n)),
            Arr(Eq(At("apply", TV(V("t")), V("univ")), At("apply", TV(At("nu", n)), V("univ"))),
                Lt(At("real", TV(V("t")), At("A", j)), At("b", j)))));
        Formula body = All("M", nat, Ex("n", nat, And(Mem(n, V("S")),
            And(Lt(V("M"), n), And(All("j", f, fibre), All("j", f, candidate))))));
        body = Arr(All("j", f, Lt(At("real", V("v"), At("A", j)), At("b", j))), body);
        body = All("b", Fn(f, V("Real")), body);
        body = Arr(All("j", f, At("Tendsto", Lam("n", At("real", TV(At("s", n)), At("A", j))),
            filter, At("nhds", At("real", V("v"), At("A", j))))), body);
        body = All("v", At("Measure", k), body);
        body = Arr(All("j", f, Ev(filter, "n", fibre)), body);
        body = Arr(All("j", f, At("IsClopen", At("A", j))), body);
        body = All("A", Fn(f, Set(k)), body);
        body = Arr(All("n", nat, Eq(At("apply", TV(At("nu", n)), Compl(At("V", n))), D(0))), body);
        body = Arr(All("n", nat, Eq(At("apply", TV(At("s", n)), V("univ")),
            At("apply", TV(At("nu", n)), V("univ")))), body);
        body = Arr(All("n", nat, Eq(Map(At("s", n), p), At("nu", n))), body);
        body = All("s", Fn(nat, SM(k)), body);
        body = All("nu", Fn(nat, SM(lspace)), body);
        body = Arr(All("n", nat, At("IsClopen", At("V", n))), body);
        body = All("V", Fn(nat, Set(lspace)), body);
        body = Arr(At("Continuous", p), body);
        body = All("p", Fn(k, lspace), body);
        body = Arr(At("Infinite", V("S")), body);
        body = All("S", Set(nat), body);
        body = Inst("Fintype", f, body);
        body = All("F", V("Type"), body);
        body = Inst("BorelSpace", lspace, body);
        body = Inst("MeasurableSpace", lspace, body);
        body = Inst("T2Space", lspace, body);
        body = Inst("TopologicalSpace", lspace, body);
        body = All("L", V("Type"), body);
        body = Inst("BorelSpace", k, body);
        body = Inst("MeasurableSpace", k, body);
        body = Inst("CompactSpace", k, body);
        body = Inst("TopologicalSpace", k, body);
        return Disp(All("K", V("Type"), body));
    }

    private static Formula TargetStatement()
    {
        var k = V("K"); var l = V("L"); var t = V("t"); var nu = V("nu");
        var mass = Eq(At("apply", TV(t), V("univ")), At("apply", TV(nu), V("univ")));
        var mapped = Eq(Map(t, V("p")), nu);
        var lower = And(Lt(Fraction(D(1,3), D(4,8)), At("apply", t, V("H"))),
            Lt(Fraction(D(1), D(6)), At("apply", t, V("H"))));
        var conclusion = Ex("H", Set(k), And(At("IsClopen", V("H")),
            And(At("Subset", V("H"), At("diff", At("preimage", V("p"), V("V")), V("R"))),
            And(Ex("B", Set(l), And(At("IsClopen", V("B")), And(At("Subset", V("B"), V("V")),
                Eq(V("H"), At("diff", At("preimage", V("p"), V("B")), V("R")))))),
                All("t", SM(k), Arr(mapped, Arr(mass, lower)))))));
        var small = All("t", SM(k), Arr(mapped, Arr(mass,
            Leq(At("real", TV(t), V("R")), Fraction(D(1), D(1,6))))));
        Formula body = Arr(small, conclusion);
        body = Arr(At("IsClopen", V("R")), body);
        body = All("R", Set(k), body);
        body = Arr(Leq(Fraction(D(1), D(2)), At("real", At("posPart", At("toJordanDecomposition", nu)), V("univ"))), body);
        body = Arr(Eq(At("apply", TV(nu), Compl(V("V"))), D(0)), body);
        body = Arr(At("IsClopen", V("V")), body);
        body = All("V", Set(l), body);
        body = Arr(At("Regular", At("negPart", At("toJordanDecomposition", nu))), body);
        body = Arr(At("Regular", At("posPart", At("toJordanDecomposition", nu))), body);
        body = All("nu", SM(l), body);
        body = Arr(At("Continuous", V("p")), body);
        body = All("p", Fn(k, l), body);
        body = Inst("ZeroDimensionalSpace", l, body);
        body = Inst("CompactSpace", l, body);
        body = Inst("BorelSpace", l, body);
        body = Inst("MeasurableSpace", l, body);
        body = Inst("T2Space", l, body);
        body = Inst("TopologicalSpace", l, body);
        body = All("L", V("Type"), body);
        body = Inst("BorelSpace", k, body);
        body = Inst("MeasurableSpace", k, body);
        body = Inst("CompactSpace", k, body);
        body = Inst("TopologicalSpace", k, body);
        return Disp(All("K", V("Type"), body));
    }

    private static Formula FiniteTargetStatement()
    {
        var k = V("K"); var l = V("L"); var nat = V("Nat"); var rows = V("Rows");
        var n = V("n"); var r = V("r"); var j = V("j"); var t = V("t");
        var x = V("x"); var y = V("y"); var p = V("p"); var wn = At("W", r, j);
        var nu = At("nu", n); var sn = At("s", n); var vn = At("V", n);
        var filter = At("inf", V("atTop"), At("principal", V("S")));
        var half = Fraction(D(1), D(2));
        var budget = At("mul", At("mul", Fraction(D(1), D(6,4)),
            At("pow", half, At("code", r))), At("pow", half, j));
        Formula Earlier(Formula b) => All("r", rows, Arr(Mem(r, V("A")),
            All("j", nat, Arr(Lt(j, V("q")), b))));
        var fibre = All("x", k, All("y", k, Arr(Mem(At("p", x), vn),
            Arr(Mem(At("p", y), vn), Arr(Eq(At("p", x), At("p", y)),
                Iff(Mem(x, wn), Mem(y, wn)))))));
        var exclusion = At("setOf", Lam("x", Ex("r", rows, And(Mem(r, V("A")),
            Ex("j", nat, And(Lt(j, V("q")), Mem(x, wn)))))));
        var candidate = All("t", SM(k), Arr(Eq(Map(t, p), nu),
            Arr(Eq(At("apply", TV(t), V("univ")), At("apply", TV(nu), V("univ"))),
                And(Lt(Fraction(D(1,3), D(4,8)), At("apply", t, V("H"))),
                    Lt(Fraction(D(1), D(6)), At("apply", t, V("H")))))));
        var literal = Ex("B", Set(l), And(At("IsClopen", V("B")), And(At("Subset", V("B"), vn),
            Eq(V("H"), At("diff", At("preimage", p, V("B")), exclusion)))));
        var pieceFibre = All("x", k, All("y", k, Arr(Mem(At("p", x), vn),
            Arr(Mem(At("p", y), vn), Arr(Eq(At("p", x), At("p", y)),
                Iff(Mem(x, V("H")), Mem(y, V("H"))))))));
        var piece = Ex("H", Set(k), And(At("IsClopen", V("H")),
            And(At("Subset", V("H"), At("diff", At("preimage", p, vn), exclusion)),
                And(literal, And(pieceFibre, candidate)))));
        Formula body = All("M", nat, Ex("n", nat,
            And(Mem(n, V("S")), And(Lt(V("M"), n), piece))));
        body = Arr(Earlier(Lt(At("real", V("v"), wn), budget)), body);
        body = Arr(Earlier(At("Tendsto", Lam("n", At("real", TV(sn), wn)),
            filter, At("nhds", At("real", V("v"), wn)))), body);
        body = All("v", At("Measure", k), body);
        body = Arr(Earlier(Ev(filter, "n", fibre)), body);
        body = Arr(All("r", rows, All("j", nat, At("IsClopen", wn))), body);
        body = All("W", Fn(rows, Fn(nat, Set(k))), body);
        body = Arr(All("n", nat, Leq(half, At("real", At("posPart", At("toJordanDecomposition", nu)), V("univ")))), body);
        body = Arr(All("n", nat, At("Regular", At("negPart", At("toJordanDecomposition", nu)))), body);
        body = Arr(All("n", nat, At("Regular", At("posPart", At("toJordanDecomposition", nu)))), body);
        body = Arr(All("n", nat, Eq(At("apply", TV(nu), Compl(vn)), D(0))), body);
        body = Arr(All("n", nat, Eq(At("apply", TV(sn), V("univ")), At("apply", TV(nu), V("univ")))), body);
        body = Arr(All("n", nat, Eq(Map(sn, p), nu)), body);
        body = All("s", Fn(nat, SM(k)), body);
        body = All("nu", Fn(nat, SM(l)), body);
        body = Arr(All("n", nat, At("IsClopen", vn)), body);
        body = All("V", Fn(nat, Set(l)), body);
        body = Arr(At("Continuous", p), body);
        body = All("p", Fn(k, l), body);
        body = Arr(At("Infinite", V("S")), body);
        body = All("S", Set(nat), body);
        body = All("q", nat, body);
        body = All("A", At("Finset", rows), body);
        body = Arr(At("Injective", V("code")), body);
        body = All("code", Fn(rows, nat), body);
        body = All("Rows", V("Type"), body);
        body = Inst("ZeroDimensionalSpace", l, body);
        body = Inst("CompactSpace", l, body);
        body = Inst("BorelSpace", l, body);
        body = Inst("MeasurableSpace", l, body);
        body = Inst("T2Space", l, body);
        body = Inst("TopologicalSpace", l, body);
        body = All("L", V("Type"), body);
        body = Inst("BorelSpace", k, body);
        body = Inst("MeasurableSpace", k, body);
        body = Inst("CompactSpace", k, body);
        body = Inst("TopologicalSpace", k, body);
        return Disp(All("K", V("Type"), body));
    }

    private static Formula GeometryStatement()
    {
        var k = V("K"); var rows = V("Rows"); var nat = V("Nat");
        var r = V("r"); var q = V("q"); var s = V("s");
        var w = At("W", r, q); var prefix = At("evenPrefix", V("H"), q);
        var evenUnion = At("setOf", Lam("x", Ex("s", nat,
            And(Eq(At("mod", s, D(2)), D(0)), Mem(V("x"), At("H", s))))));
        var traces = All("r", rows, All("q", nat, Arr(Lt(At("code", r), q),
            And(Eq(Inter(V("Z"), w), Inter(prefix, w)),
            And(Eq(Inter(V("Y"), w), Inter(Compl(prefix), w)),
            And(At("Disjoint", Inter(V("Y"), V("Z")), w),
                All("x", At("Subtype", At("splitCarrier", V("Y"), V("Z"))),
                    Arr(Mem(At("fst", At("val", V("x"))), w),
                        Iff(Eq(At("snd", At("val", V("x"))), V("true")),
                            Mem(At("fst", At("val", V("x"))), prefix))))))))));
        var targetTraces = All("q", nat,
            And(Eq(Inter(V("Z"), At("T", q)), At("ite", Eq(At("mod", q, D(2)), D(0)), At("H", q), V("empty"))),
            And(At("Disjoint", Inter(V("Y"), V("Z")), At("T", q)),
            All("x", At("Subtype", At("splitCarrier", V("Y"), V("Z"))),
                Arr(Mem(At("fst", At("val", V("x"))), At("T", q)),
                    Iff(Eq(At("snd", At("val", V("x"))), V("true")),
                        And(Eq(At("mod", q, D(2)), D(0)), Mem(At("fst", At("val", V("x"))), At("H", q)))))))));
        var result = Ex("Y", Set(k), Ex("Z", Set(k),
            And(At("IsClosed", V("Y")), And(At("IsClosed", V("Z")),
            And(Eq(At("union", V("Y"), V("Z")), V("univ")),
            And(Eq(V("Z"), At("closure", evenUnion)),
            And(Eq(V("Y"), At("closure", Compl(V("Z")))),
            And(At("IsClosed", At("splitCarrier", V("Y"), V("Z"))),
            And(At("Surjective", Lam("x", At("fst", At("val", V("x"))))), And(traces, targetTraces))))))))));
        var avoidance = All("r", rows, All("q", nat, All("s", nat,
            Arr(Lt(At("code", r), q), Arr(Lt(q, s),
                At("Disjoint", At("H", s), w))))));
        Formula body = Arr(All("q", nat, At("Subset", At("H", q), At("T", q))), result);
        body = Arr(At("Pairwise", Lam("q", Lam("s", At("Disjoint", At("T", q), At("T", s))))), body);
        body = Arr(All("q", nat, At("IsClopen", At("T", q))), body);
        body = All("T", Fn(nat, Set(k)), body);
        body = Arr(avoidance, body);
        body = Arr(All("r", rows, All("q", nat, At("IsClopen", w))), body);
        body = All("W", Fn(rows, Fn(nat, Set(k))), body);
        body = Arr(All("q", nat, At("IsClopen", At("H", q))), body);
        body = All("H", Fn(nat, Set(k)), body);
        body = All("code", Fn(rows, nat), body);
        body = All("Rows", V("Type"), body);
        body = Inst("TopologicalSpace", k, body);
        return Disp(All("K", V("Type"), body));
    }

    private static Formula SplitStatement()
    {
        var point = Or(And(Mem(At("fst", V("p")), V("Y")),
            Eq(At("snd", V("p")), V("false"))),
            And(Mem(At("fst", V("p")), V("Z")), Eq(At("snd", V("p")), V("true"))));
        Formula body = Eq(At("splitCarrier", V("Y"), V("Z")), At("setOf", Lam("p", point)));
        body = All("Z", Set(V("K")), body);
        body = All("Y", Set(V("K")), body);
        return Disp(All("K", V("Type"), body));
    }

    private static Formula PrefixStatement()
    {
        var pred = Ex("s", V("Nat"), And(Lt(V("s"), At("add", V("q"), D(1))),
            And(Eq(At("mod", V("s"), D(2)), D(0)), Mem(V("x"), At("H", V("s"))))));
        Formula body = Eq(At("evenPrefix", V("H"), V("q")), At("setOf", Lam("x", pred)));
        body = All("q", V("Nat"), body);
        body = All("H", Fn(V("Nat"), Set(V("K"))), body);
        return Disp(All("K", V("Type"), body));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed finite signed marginals and exact clopen traces in ordered closed splits.",
        H("Finite marginals and ordered split geometry"),
        Blocks(
            Paragraph(Text("K is a compact Borel space. L is a Hausdorff Borel space and p is continuous. "
                + "The measures are arbitrary real SignedMeasure values. A candidate and its reference have the same signed base projection and the same total variation mass as that base measure. "
                + "The base variation vanishes outside the given clopen support. Each fixed Boolean coordinate eventually becomes constant on the whole base fibres in that support.")),
            Describe.Lean(DescribeId.Create("uniform-finite-marginal"),
                DeclarationHandle.Create(Owner + "eventually_uniform_finite_marginal"),
                H("Uniform fixed finite signed marginals"), StatementSource.FromAuthor(UniformStatement()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For the finite coordinate map, each clopen atom has the same signed mass for every admissible lift. "
                        + "The signed reference limit gives convergence on these finitely many atoms. Summing their absolute differences computes the total variation mass of the finite signed difference and makes the estimate uniform over all lifts.")),
                    Paragraph(Text("Exact mass preservation for p separately identifies the pushed positive variations. Applying whole-fibre constancy to their clopen tests proves equality of the positive finite marginals. "
                        + "No preservation of variation by the finite-coordinate map is asserted: it can identify opposite signed atoms. The finite coordinate type may be empty and the filter is arbitrary."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("auxiliary-index"),
                DeclarationHandle.Create(Owner + "exists_auxiliary_index"),
                H("Auxiliary index in the prescribed infinite reservoir"), StatementSource.FromAuthor(AuxiliaryStatement()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Fix the finite Boolean coordinate family before choosing the next index. The reservoir S is any infinite subset of the natural numbers, such as one of the inherited fixed parity pools. "
                        + "Reference signed convergence and whole-fibre coordinate constancy hold along atTop intersect principal(S). The pulled-back row supports are pairwise disjoint, and v is any finite positive measure on K.")),
                    Paragraph(Text("Their v masses form a summable sequence and tend to zero. The uniform fixed-marginal estimate, all finitely many coordinate conditions, this small-mass tail and the lower index bound hold together eventually in S. "
                        + "Infinitude supplies a member beyond the resulting finite threshold. The chosen index retains the original reservoir; it satisfies both signed and positive marginal conclusions without changing a parity set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("target-index"),
                DeclarationHandle.Create(Owner + "exists_target_index"),
                H("Target index for all fixed finite exclusions"), StatementSource.FromAuthor(TargetIndexStatement()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Fix a finite family of clopen sets A(j). The positive variation evaluations of the reference lifts converge on these fixed sets to v(A(j)), each strictly below its prescribed bound b(j). "
                        + "Whole-fibre constancy for membership in every A(j) holds eventually in the infinite reservoir S. Exact preservation of base variation transfers each reference evaluation to every signed lift in its norm-preserving class.")),
                    Paragraph(Text("A finite intersection of the resulting eventual conditions and a lower index bound leaves an infinite tail in S. One target index therefore controls every exclusion simultaneously for every signed lift. "
                        + "The same selected index retains whole-fibre constancy of every exclusion. The family may be empty. The input is fixed-test convergence of positive variations; it assumes neither a moving-test estimate nor a signed weak-star limit for those variations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-target-piece"),
                DeclarationHandle.Create(Owner + "exists_signed_target_piece"),
                H("Signed target piece after exclusion"), StatementSource.FromAuthor(TargetStatement()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The target is an arbitrary real signed measure nu on a compact Hausdorff zero-dimensional Borel space L. Its Jordan parts are regular, its variation vanishes off the clopen V, and its positive mass is at least one half. "
                        + "The continuous p maps K to L. For every lift preserving signed projection and total variation mass, the clopen exclusion R has variation mass at most one sixteenth.")),
                    Paragraph(Text("Positive-clopen approximation gives a clopen B inside V with nu(B) greater than one third. Put H=p inverse(B) minus R. For every such signed lift t, its mass on p inverse(B) is nu(B), while t on the removed intersection is at most its variation on R. "
                        + "Thus t(H) is greater than one third minus one sixteenth, namely thirteen forty-eighths, which is greater than one sixth. The selected H is shared by all lifts. The output retains the clopen B, its containment in V, and the literal equation H=p inverse(B) minus R."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-exclusion-target"),
                DeclarationHandle.Create(Owner + "exists_target_after_finite_exclusion"),
                H("Target after the finite earlier exclusions"), StatementSource.FromAuthor(FiniteTargetStatement()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The finite row set A and earlier columns j<q are fixed before the target index is selected. Distinct row codes give the budget (1/64)(1/2)^(code(r))(1/2)^j. The sum of all such budgets is at most one sixteenth, including when A or the earlier column set is empty.")),
                    Paragraph(Text("The positive reference variation on each fixed clopen exclusion is strictly below its budget. Positive-variation convergence and whole-fibre constancy select one larger target index for which every signed norm-preserving lift obeys all those bounds. Finite subadditivity therefore bounds the variation of their whole union by one sixteenth. Positive clopen approximation then constructs the common H outside the union with signed mass greater than thirteen forty-eighths, hence greater than one sixth, for every lift. The literal base slice is retained, and the earlier exclusion tests prove whole-target-fibre constancy of H at this same selected index."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-split-carrier"),
                DeclarationHandle.Create(Owner + "splitCarrier"), H("Literal split carrier"),
                StatementSource.FromAuthor(SplitStatement()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The carrier is a literal subset of K times Bool. Points on the zero side lie over Y and points on the one side lie over Z."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-even-prefix"), DeclarationHandle.Create(Owner + "evenPrefix"),
                H("Finite even prefix"), StatementSource.FromAuthor(PrefixStatement()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The union ranges over s in range(q+1), retaining H(s) exactly when s modulo two is zero. It is clopen when each H(s) is clopen."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordered-closed-split"),
                DeclarationHandle.Create(Owner + "exists_closed_split_of_ordered_exclusion"),
                H("Closed split from ordered exclusion"), StatementSource.FromAuthor(GeometryStatement()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For each row r and active column q, every later H(s) avoids the entire clopen support W(r,q). "
                        + "Consequently the union of all even H(s) and its finite even prefix have exactly the same trace on W(r,q). Closure preserves this trace because both the support and the finite prefix are clopen.")),
                    Paragraph(Text("Define Z as the closure of the full even union and Y as the closure of its complement. These closed sets cover K. "
                        + "Their local traces are complementary, so their common boundary avoids each active support. The literal split is closed, its first projection is surjective, and its new Boolean coordinate on an active support is precisely membership in the finite prefix. "
                        + "Pairwise disjoint clopen target supports T(q), with H(q) contained in T(q), have exact traces H(q) on even q and the empty set on odd q, including q=0. Their boundaries are excluded as well. The row type can be finite, including a single row."))), DescribeRole.Theorem))));
}
