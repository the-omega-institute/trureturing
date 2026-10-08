using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ActualControlSlotsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "General-base stationary execution constructs its actual directed reading-slot graph and capacity bounds.",
        H("Actual reading slots and stationary control capacity"),
        Blocks(
            Paragraph(Text(
                "For p at least two and positive P, the source is ZMod(pP), and its digit "
                + "is floor(val/P) in Fin p. The width P may in particular be p to any "
                + "nonnegative integer power. A controller has one source-independent initial "
                + "control and fixed total action, wait-successor, digit-row-successor and "
                + "output functions. The three actions partition Q into read, wait and halt. "
                + "Wait increments the source by one; read preserves it. Halt is absorbing "
                + "in the mathematical trajectory and emits no action.")),
            Paragraph(Text(
                "Correct supplies a finite stop time for every original source, fixed terminal "
                + "decoding of that original source, and no earlier halt. The initial action "
                + "is a read, a positive wait separates reads, and the final action is a read. "
                + "Used(q,b) means an actual read at q with digit b. Waiting(q) means an actual "
                + "wait at q. Terminal(q,b) adds that the fixed digit-row successor halts. "
                + "Write R for the subtype of controls with at least one used digit.")),
            Paragraph(Text(
                "For p=3 and P>1, StationaryUnitControl.Controller has the same operational "
                + "table: its wait instruction supplies action and waitNext, its read row "
                + "supplies action and readNext, and its halt label supplies action and output. "
                + "Inactive function entries may be filled arbitrarily. The digit functions "
                + "agree, and this step equals that model's total absorbing next function. "
                + "The present model also admits P=1 and arbitrary alphabet sizes.")),
            Paragraph(Text(
                "Occurs(x,t,u) means t is before the stop on original input x, the control "
                + "is the control of slot u, and the physical digit is its digit. Edge(u,v) "
                + "means two such occurrences on the same original input at times i<j, "
                + "with every intermediate action a wait. Edges count distinct slot pairs, "
                + "including repeated pairs only once. Reading-control revisits and mergers "
                + "are unrestricted.")),
            Describe.Lean(DescribeId.Create("actual-control-slot-capacity"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/ActualControlSlots.result"),
                H("The actual graph, exact identity, and capacity bounds"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The graph G has exactly the actual used slots and actual next-read edges. "
                    + "Its root is the common start. Every active slot follows a fixed positive "
                    + "wait chain to one target read control, with at most two cyclically adjacent "
                    + "digits. Final slots biject with original sources. The start cannot recur, "
                    + "since every physical value already occurs there initially. Every other "
                    + "reading control has a distinct actual immediate wait predecessor. "
                    + "Incidence accounting gives the displayed identity and the binary lower "
                    + "bound. For odd p, the target deficit yields the final product inequality, "
                    + "equivalently r at least 1 plus 2p(P-1)/(p-1). Natural subtraction is used "
                    + "throughout. Here r is NatCard(R), and w counts Waiting controls."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var r = Call("NatCard", Reads);
        var w = Call("NatCard", Set("q", V("Q"), Call("Waiting", V("C"), V("I"), V("q"))));
        var slot = Seq(Reads, Times, Sp, Call("Fin", V("p")));
        var u = V("u");
        var v = V("v");
        var z = Sum("missing");
        var h = Sum("excess");
        var n = Sum("singles");
        var local = All("q", Reads, Imp(Ne(V("q"), Call("root", V("G"))),
            LE(D(1), Add(At("missing"), At("excess"), At("singles")))));
        var adjacent = All("u", slot, Imp(Call("Nonempty", Call("next", V("G"), u)),
            Ex("q", Reads, Ex("b", Call("Fin", V("p")), Ex("c", Call("Fin", V("p")), And(
                Seq(Call("next", V("G"), u), Subseteq,
                    Seq(OpenBrace, Pair(V("q"), V("b")), Comma, Pair(V("q"), V("c")), CloseBrace)),
                EqF(Call("val", V("c")), Call("mod", Add(Call("val", V("b")), D(1)), V("p")))))))));
        var body = And(
            EqF(Call("val", Call("root", V("G"))), Call("initial", V("C"))),
            All("u", slot, Seq(Grp(Member(u, Call("used", V("G")))), Iff, Grp(
                Ex("x", Source, Ex("t", N, Call("Occurs", V("C"), V("I"), V("x"), V("t"), u)))))),
            All("u", slot, All("v", slot, Seq(Grp(Member(v, Call("next", V("G"), u))), Iff,
                Grp(Call("Edge", V("C"), V("I"), u, v))))),
            adjacent,
            EqF(Call("terminalCount", V("G")), Mul(V("p"), V("P"))),
            EqF(Call("NatCard", Set("s", Seq(V("Q"), Times, Sp, Call("Fin", V("p"))),
                Call("Terminal", V("C"), V("I"), Call("fst", V("s")), Call("snd", V("s"))))),
                Mul(V("p"), V("P"))),
            All("x", Source, All("t", N, Imp(LE(V("t"), Call("length", V("I"), V("x"))),
                Imp(EqF(Call("snd", Call("run", V("C"), V("hp"), V("hP"), V("x"), V("t"))),
                    Call("initial", V("C"))), EqF(V("t"), D(0)))))),
            LE(Sub(r, D(1)), w),
            EqF(Mul(V("p"), r), Add(Sub(Mul(D(2), Mul(V("p"), V("P"))), V("p")), h, n, z)),
            LE(Sub(Mul(D(2), V("P")), D(1)), r),
            Imp(Call("Odd", V("p")), And(local, LE(Sub(r, D(1)), Add(z, h, n)),
                LE(Mul(Mul(D(2), V("p")), Sub(V("P"), D(1))),
                    Mul(Sub(V("p"), D(1)), Sub(r, D(1)))))));
        return All("p", N, All("P", N, All("Q", V("Type"),
            All("hp", LE(D(2), V("p")), All("hP", LT(D(0), V("P")),
            All("C", Call("Controller", V("p"), V("P"), V("Q")),
            All("I", Call("Correct", V("C"), V("hp"), V("hP")), Seq(
                OpenBracket, Call("Fintype", V("Q")), CloseBracket,
                OpenBracket, Call("DecidableEq", V("Q")), CloseBracket,
                Grp(Ex("G", Call("SlotGraph", V("p"), Reads), body))))))))));
    }
    private static Formula V(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Source => Call("ZMod", Mul(V("p"), V("P")));
    private static Formula Reads => Set("q", V("Q"), Ex("b", Call("Fin", V("p")),
        Call("Used", V("C"), V("I"), V("q"), V("b"))));
    private static Formula Set(string s, Formula type, Formula predicate) =>
        Seq(OpenBrace, V(s), Colon, type, Mid, Sp, predicate, CloseBrace);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Member(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Grp(a), Times, Sp, Grp(b));
    private static Formula EqF(Formula a, Formula b) => Seq(Grp(a), Eq, Grp(b));
    private static Formula LE(Formula a, Formula b) => Seq(Grp(a), Le, Sp, Grp(b));
    private static Formula LT(Formula a, Formula b) => Seq(Grp(a), Lt, Grp(b));
    private static Formula Ne(Formula a, Formula b) => Seq(Grp(a), Neq, Sp, Grp(b));
    private static Formula Sub(Formula a, Formula b) => Seq(Grp(a), Minus, Grp(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, type, Comma, Grp(body));
    private static Formula Ex(string s, Formula type, Formula body) =>
        Seq(Exists, Sp, V(s), Colon, type, Comma, Grp(body));
    private static Formula At(string s) => Call(s, V("G"), V("q"));
    private static Formula Sum(string s) => Seq(F.Sum, Underscore,
        Grp(Seq(V("q"), InMacro, Sp, Reads)), At(s));
    private static Formula Join(Formula separator, Formula[] args) =>
        Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { separator, x })]);
    private static Formula Add(params Formula[] args) => Join(Plus, args);
    private static Formula And(params Formula[] args) => Join(Land, [.. args.Select(x => Grp(x))]);
    private static Formula Call(string s, params Formula[] args) =>
        Seq(Operatorname, Sp, Grp(V(s)), Open, Join(Comma, args), Close);
}
