using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class SaturatedActualConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Saturation exhausts actual child event fibers and prevents cycles, shared children and shared next-reading targets.",
        H("Complete saturated actual cones"),
        Blocks(
            Paragraph(Text(
                "The Controller and Correct structures describe one stationary table on ZMod(pP), "
                + "with p at least two, P positive, and a first action that reads. Each initialized "
                + "input follows its original physical run to a fixed correct output. A slot consists "
                + "of an actually used reading control and a physical digit. events(u) contains every "
                + "pair of original input and physical time at that slot, including repeated visits "
                + "by the same input. readIndex(e) counts reads up to and including that event. "
                + "At a common read deadline h, mass(u) is the sum of two to the negative remaining "
                + "read allowance over this entire event set.")),
            Paragraph(Text(
                "The actual Edge relation joins consecutive reads on the same original input, "
                + "with only actual waits in between. Reach is its reflexive transitive closure; "
                + "Loop is its transitive closure from a slot to itself. Halting at a slot means "
                + "that its fixed read successor halts immediately. A ConeTree expands all actual children at each fork and retains a singleton event at each terminal leaf. leafCount and internalCount count its leaves and forks. Neither unique incoming "
                + "edges nor absence of cycles is a premise.")),
            Describe.Lean(DescribeId.Create("saturated-actual-cone"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/SaturatedActualCone.result"),
                H("Complete child transport and distinct actual targets"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Encode each actual future by one binary symbol per subsequent read. The "
                    + "actual successor set has at most two elements. A common future prefix "
                    + "determines the same terminal label; uniqueness of consecutive reads also "
                    + "identifies the physical event. Thus these binary words are distinct and "
                    + "prefix-free. Kraft's inequality gives the complete slot mass bound. "
                    + "Advancing every event of a saturated active slot doubles its mass and "
                    + "injects it into at most two complete child fibers, each of mass at most one. "
                    + "Both fibers must have mass one, and positivity excludes every omitted "
                    + "event. Literal waiting tails give a common positive delay. This complete "
                    + "transport raises the minimum read index and identifies the sole predecessor "
                    + "of each child. Consequently the whole successor cone has no cycle or "
                    + "reconvergence. An initialized input cannot return to a saturated slot, so the "
                    + "original-input projection is injective on every complete cone fiber. At a terminal slot the complete event fiber is a singleton; "
                    + "mass one forces its read index to equal h. Equality in the mass bound "
                    + "also forces every represented original run to use exactly h reads. "
                    + "When p is at most three, two "
                    + "pairs of child digits at a common reading control intersect, so predecessor "
                    + "uniqueness identifies their parent slots. Every next-reading target differs "
                    + "from the initial control. Strict growth of the minimum read index "
                    + "constructs a finite complete binary expansion. Exhaustive event transport "
                    + "preserves counts across forks, giving m leaves and m minus one forks "
                    + "when the entrance has m events."))), DescribeRole.Theorem),
            Paragraph(Text(
                "This statement covers two and three physical digits, and retains the "
                + "original positive waiting durations. It treats an initial read, so a positive "
                + "common initial waiting prefix is outside its model. An ordering of leaves by original low phase and its leaf-depth "
                + "correspondence and the gap-cost inequalities are additional assertions.")))));

    private static Formula Statement()
    {
        var u = V("u");
        var v = V("v");
        var w = V("w");
        var a = V("a");
        var b = V("b");
        var l = V("l");
        var r = V("r");
        var e = V("e");
        var d = V("d");
        var t = V("t");
        var delta = V("delta");
        var leaf = Ex("e", Event, And(
            EqF(Events(v), Seq(OpenBrace, e, CloseBrace)),
            EqF(Index(e), V("h")),
            EqF(Add(Snd(e), D(1)), Call("length", V("I"), Fst(e)))));
        var waits = All("t", N, Imp(LT(Snd(d), t), Imp(LT(t, Snd(e)),
            EqF(Call("action", V("C"), Snd(Call("run", V("hp"), V("hP"), V("C"), Fst(d), t))),
                Call("wait")))));
        var transport = All("e", Event,
            Imp(Member(e, Call("union", Events(l), Events(r))),
                Ex("d", Event, And(Member(d, Events(v)), EqF(Fst(e), Fst(d)),
                    EqF(Snd(e), Add(Add(Snd(d), D(1)), delta)), waits))));
        var children = Ex("l", Slot, Ex("r", Slot, Ex("delta", N, And(
            NE(l, r), LT(D(0), delta), Edge(v, l), Edge(v, r),
            EqF(Mass(l), D(1)), EqF(Mass(r), D(1)),
            All("z", Slot, IFF(Edge(v, V("z")), OrF(EqF(V("z"), l), EqF(V("z"), r)))),
            transport))));
        var incoming = All("w", Slot, Imp(Edge(v, w), And(
            All("z", Slot, Imp(Edge(V("z"), w), EqF(V("z"), v))),
            NE(Call("val", Fst(w)), Call("initial", V("C"))))));
        var originals = All("e", Event, Imp(Member(e, Events(v)),
            All("d", Event, Imp(Member(d, Events(v)),
                Imp(EqF(Fst(e), Fst(d)), EqF(e, d))))));
        var cone = All("v", Slot, Imp(Reach(u, v), And(
            EqF(Mass(v), D(1)),
            All("e", Event, Imp(Member(e, Events(v)), EqF(
                Call("card", Call("readEvents", V("hp"), V("hP"), V("C"), V("I"), Fst(e))), V("h")))),
            originals, Seq(Neg, Sp, Grp(Loop(v))),
            Imp(Halt(v), leaf), Imp(Seq(Neg, Sp, Grp(Halt(v))), children), incoming)));
        var targets = Bind(Imp(Reach(u, v), Imp(Reach(u, w), Imp(Edge(v, a), Imp(Edge(w, b),
            Imp(EqF(Fst(a), Fst(b)), EqF(v, w)))))),
            ("v", Slot), ("w", Slot), ("a", Slot), ("b", Slot));
        var tree = Ex("T", Call("ConeTree", V("hp"), V("hP"), V("C"), V("I"), u), And(
            EqF(Call("leafCount", V("hp"), V("hP"), V("C"), V("I"), V("T")), Call("card", Events(u))),
            EqF(Add(Call("internalCount", V("hp"), V("hP"), V("C"), V("I"), V("T")), D(1)),
                Call("leafCount", V("hp"), V("hP"), V("C"), V("I"), V("T")))));
        var conclusion = And(LE(D(2), Call("card", Events(u))), cone, targets, tree);
        var hypotheses = Imp(All("x", Source,
            LE(Call("card", Call("readEvents", V("hp"), V("hP"), V("C"), V("I"), V("x"))), V("h"))),
            Imp(LE(V("p"), D(3)), All("u", Slot, Imp(Seq(Neg, Sp, Grp(Halt(u))),
                Imp(EqF(Mass(u), D(1)), conclusion)))));
        var body = All("h", N, hypotheses);
        body = Seq(OpenBracket, Call("Fintype", V("Q")), CloseBracket,
            OpenBracket, Call("DecidableEq", V("Q")), CloseBracket, Grp(body));
        return Bind(body, ("p", N), ("P", N), ("Q", V("Type")),
            ("hp", LE(D(2), V("p"))), ("hP", LT(D(0), V("P"))),
            ("C", Call("Controller", V("p"), V("P"), V("Q"))),
            ("I", Call("Correct", V("C"), V("hp"), V("hP"))));
    }

    private static Formula Source => Call("ZMod", Seq(V("p"), Times, Sp, V("P")));
    private static Formula Slot => Seq(Open, OpenBrace, V("q"), Colon, V("Q"), Mid, Sp,
        Ex("b", Call("Fin", V("p")), Call("Used", V("C"), V("I"), V("q"), V("b"))),
        CloseBrace, Close, Times, Sp, Call("Fin", V("p")));
    private static Formula Event => Seq(Grp(Source), Times, Sp, N);
    private static Formula Events(Formula v) => Call("events", V("hp"), V("hP"), V("C"), V("I"), v);
    private static Formula Mass(Formula v) => Call("mass", V("hp"), V("hP"), V("C"), V("I"), V("h"), v);
    private static Formula Index(Formula e) => Call("readIndex", V("hp"), V("hP"), V("C"), V("I"), e);
    private static Formula Edge(Formula a, Formula b) => Call("Edge", V("C"), V("I"), a, b);
    private static Formula Reach(Formula a, Formula b) => Call("ReflTransGen", Call("Edge", V("C"), V("I")), a, b);
    private static Formula Loop(Formula a) => Call("TransGen", Call("Edge", V("C"), V("I")), a, a);
    private static Formula Halt(Formula v) => EqF(Call("action", V("C"),
        Call("readNext", V("C"), Call("val", Fst(v)), Snd(v))), Call("halt"));
    private static Formula Fst(Formula x) => Call("fst", x);
    private static Formula Snd(Formula x) => Call("snd", x);
    private static Formula V(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula EqF(Formula a, Formula b) => Seq(Grp(a), Eq, Grp(b));
    private static Formula LE(Formula a, Formula b) => Seq(Grp(a), Le, Sp, Grp(b));
    private static Formula LT(Formula a, Formula b) => Seq(Grp(a), Lt, Grp(b));
    private static Formula NE(Formula a, Formula b) => Seq(Grp(a), Neq, Sp, Grp(b));
    private static Formula IFF(Formula a, Formula b) => Seq(Grp(a), Iff, Grp(b));
    private static Formula OrF(Formula a, Formula b) => Seq(Grp(a), Lor, Grp(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(Grp(a), Plus, Grp(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, t, Comma, Grp(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, t, Comma, Grp(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Sp, Grp(b));
    private static Formula Bind(Formula b, params (string Name, Formula Type)[] binders)
    {
        for (var i = binders.Length - 1; i >= 0; i--) b = All(binders[i].Name, binders[i].Type, b);
        return b;
    }
    private static Formula Join(Formula separator, Formula[] args) =>
        Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { separator, x })]);
    private static Formula And(params Formula[] xs) => Join(Land, [.. xs.Select(x => Grp(x))]);
    private static Formula Call(string n, params Formula[] xs) => Seq(Operatorname, Sp, Grp(V(n)), Open, Join(Comma, xs), Close);
}
