using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class SharedCarryEvenControllerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An even-base shared stationary table stops at the first carry and decodes the original source.",
        H("Shared first-carry acquisition in even bases"),
        Blocks(
            Paragraph(Text(
                "The base p is any even integer at least two, and P is any positive integer. "
                + "The source is ZMod(pP), read returns floor(val/P), and wait adds one. "
                + "The table uses ActualControlSlots.Controller and its Correct contract: "
                + "the initial action is read, positive waits separate reads, the last action "
                + "is read, every input halts in finite time, and its terminal control alone "
                + "outputs that original input. In particular the construction applies when P is p to any nonnegative power.")),
            Paragraph(Text(
                "State(p,P,Colors) is the disjoint sum of Unit, Colors times Bool, and ZMod(pP). "
                + "The Unit control is the initial read. Each color has a wait control (false) "
                + "and a read control (true); each source label has a halt control. Here Colors "
                + "is Fin(P-1) times Fin 2. At positive scan time t, color(b,t-1) is "
                + "(t-1,b mod 2). All these nominal controls count toward capacity.")),
            Paragraph(Text(
                "For P greater than one, the initial digit b selects the wait control of "
                + "color(b,0). A wait increments the source and selects its own color's read "
                + "control. In the row indexed by (t-1,e), a digit d with d mod 2=e has "
                + "no carry: it selects color(d,t)'s wait if t<P-1, and otherwise the halt "
                + "label dP. A digit with opposite parity has carried: its predecessor is "
                + "p-1 when d=0, and d-1 otherwise, and the row selects the halt label "
                + "predecessor(d)P+(P-t). Thus every row is a fixed total function of its "
                + "own index, color and digit. For p=2, the two wrap occurrences have "
                + "distinct colors even though both use the same pair of digits.")),
            Paragraph(Text(
                "Halt controls output their labels and have themselves as both formal "
                + "successors; unused read successors of wait controls select the existing halt label zero. "
                + "For P=1, the initial read immediately halts with its digit as label. "
                + "Writing r=val(x) mod P, waits(x) is P-1 if r=0 and P-r otherwise. "
                + "The certified execution has length 2 waits(x)+1. The source after t waits "
                + "is x+t, and the read at that point distinguishes no carry from the first "
                + "carry. Both routes halt at the label x.")),
            Paragraph(Text(
                "eventCount(hp,hP,C,I,x,a) is the cardinality of the times before I.length(x) "
                + "at which action(run(x,t)) equals a. It counts actual issued actions; "
                + "the halt event itself is excluded. Natural subtraction is used in the "
                + "capacity and wait bounds below.")),
            Describe.Lean(DescribeId.Create("shared-carry-even-controller"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/SharedCarryEvenController.result"),
                H("One correct total table with exact capacity and worst counts"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the same table and correctness certificate I, the total nominal "
                    + "capacity is pP+4P-3. Every input uses at most P reads and P-1 waits, "
                    + "and one input simultaneously attains both bounds: the original zero "
                    + "source has no carry before the last scan. At P=1 the capacity is p+1. "
                    + "This asserts the capacity and correctness of the constructed table. "
                    + "Minimization over controllers allowing initial wait prefixes requires "
                    + "a separate prefix-normalization statement."))), DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var table = Call("table", V("p"), V("P"));
        var colors = Mul(Call("Fin", Sub(V("P"), D(1))), Call("Fin", D(2)));
        var capacity = Call("NatCard", Call("State", V("p"), V("P"), colors));
        var source = Call("ZMod", Mul(V("p"), V("P")));
        Formula Count(string action) => Call("eventCount", V("hp"), V("hP"),
            table, V("I"), V("x"), Call(action));
        var body = And(
            EqF(capacity, Sub(Add(Mul(V("p"), V("P")), Mul(D(4), V("P"))), D(3))),
            All("x", source, And(LE(Count("read"), V("P")),
                LE(Count("wait"), Sub(V("P"), D(1))))),
            Ex("x", source, And(EqF(Count("read"), V("P")),
                EqF(Count("wait"), Sub(V("P"), D(1))))),
            Imp(EqF(V("P"), D(1)), EqF(capacity, Add(V("p"), D(1)))));
        return All("p", N, All("P", N,
            All("hp", LE(D(2), V("p")), All("hP", LT(D(0), V("P")),
                Imp(Call("Even", V("p")),
                    Ex("I", Call("Correct", table, V("hp"), V("hP")), body))))));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Join(Formula separator, Formula[] args) =>
        Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { separator, x })]);
    private static Formula Call(string s, params Formula[] args) =>
        Seq(Operatorname, Sp, Grp(V(s)), Open, Join(Comma, args), Close);
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, type, Comma, Grp(body));
    private static Formula Ex(string s, Formula type, Formula body) =>
        Seq(Exists, Sp, V(s), Colon, type, Comma, Grp(body));
    private static Formula EqF(Formula a, Formula b) => Seq(Grp(a), Eq, Grp(b));
    private static Formula LE(Formula a, Formula b) => Seq(Grp(a), Le, Sp, Grp(b));
    private static Formula LT(Formula a, Formula b) => Seq(Grp(a), Lt, Grp(b));
    private static Formula Mul(Formula a, Formula b) => Seq(Grp(a), Times, Sp, Grp(b));
    private static Formula Sub(Formula a, Formula b) => Seq(Grp(a), Minus, Grp(b));
    private static Formula Add(Formula a, Formula b) => Seq(Grp(a), Plus, Grp(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula And(params Formula[] args) => Join(Land, [.. args.Select(x => Grp(x))]);
}
