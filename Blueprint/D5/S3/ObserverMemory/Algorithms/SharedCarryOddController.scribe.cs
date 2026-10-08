using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class SharedCarryOddControllerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd-base shared total stationary table decodes the original source at its first carry.",
        H("Shared first-carry acquisition in odd bases"),
        Blocks(
            Paragraph(Text(
                "Let a be positive, p=2a+1, and P be positive with a dividing P-1. "
                + "The usual widths P=p^k satisfy the stronger divisibility p-1 divides P-1. "
                + "The physical source is ZMod(pP), read returns floor(val/P), and a unit wait "
                + "adds one. The table satisfies ActualControlSlots.Controller.Correct: "
                + "every original input halts with that input as its terminal control label, "
                + "the first and last actions are reads, and positive waits separate reads.")),
            Paragraph(Text(
                "The colors are Fin((P-1)/a) times ZMod(p). For time t=i+1, "
                + "color(b,i)=(floor(i/a), b-2(i mod a)-1 modulo p). Fixing a color "
                + "(g,v), its edges have endpoints v+2u+1 and v+2u+2 modulo p, "
                + "where 0<=u<a. They form a near-perfect matching, missing only v. "
                + "The carrier reuses State(p,P,Colors): one initial read control, one "
                + "wait/read pair for every color, and one halt control for every source label.")),
            Paragraph(Text(
                "At the initial read, a width greater than one sends digit b to the wait "
                + "control for color(b,0). At width one it immediately halts with label b. "
                + "A colored wait increments the physical source and selects its colored read. "
                + "In read row (g,v), digit d gives j=(d-v modulo p). If j=0, the unused "
                + "slot selects the existing halt label zero. Otherwise the fixed occurrence "
                + "index is i=ga+floor((j-1)/2). An odd j is the no-carry endpoint: it "
                + "selects color(d,i+1)'s wait when i+2<P, or halts with label dP. "
                + "An even j is the carry endpoint: it halts with label predecessor(d)P+P-(i+1). "
                + "The predecessor is p-1 at d=0 and d-1 otherwise. All halt successors are themselves; "
                + "the unused read successors of wait controls select halt label zero. "
                + "Thus every action and both formal successors are total on the nominal carrier.")),
            Paragraph(Text(
                "For x=bP+r, the stopping wait count is P-1 when r=0 and P-r otherwise. "
                + "The same stationary row recovers its occurrence from either matching endpoint. "
                + "The actual trajectory never uses the missing slot and halts at H_x after "
                + "2 waits(x)+1 issued actions. eventCount counts actual actions before this halt. "
                + "There are p(P-1)/a colors and two controls per color. Natural division "
                + "and subtraction are used in the capacity formula.")),
            Describe.Lean(DescribeId.Create("shared-carry-odd-controller"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/SharedCarryOddController.result"),
                H("One correct total table with exact capacity and worst counts"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same table and certificate simultaneously give the stated capacity, "
                    + "the bounds for every input, and an input attaining both worst counts. "
                    + "The zero input attains P reads and P-1 waits. At width one the capacity is p+1. "
                    + "This is an attainment construction; minimization over controllers that allow "
                    + "an initial wait prefix requires a separate prefix-normalization statement."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var p = Add(Mul(D(2), V("a")), D(1));
        var table = Call("table", V("a"), V("P"), V("ha"), V("hd"));
        var colors = Mul(Call("Fin", Call("NatDiv", Sub(V("P"), D(1)), V("a"))),
            Call("ZMod", p));
        var capacity = Call("NatCard", Call("State", p, V("P"), colors));
        var source = Call("ZMod", Mul(p, V("P")));
        Formula Count(string action) => Call("eventCount", Call("proof", LE(D(2), p)),
            V("hP"), table, V("I"), V("x"), Call(action));
        var body = And(
            EqF(capacity, Add(Add(Mul(p, V("P")), D(1)),
                Call("NatDiv", Mul(Mul(D(4), p), Sub(V("P"), D(1))), Sub(p, D(1))))),
            All("x", source, And(LE(Count("read"), V("P")),
                LE(Count("wait"), Sub(V("P"), D(1))))),
            Ex("x", source, And(EqF(Count("read"), V("P")),
                EqF(Count("wait"), Sub(V("P"), D(1))))),
            Imp(EqF(V("P"), D(1)), EqF(capacity, Add(p, D(1)))));
        return All("a", N, All("P", N,
            All("ha", LT(D(0), V("a")),
                All("hd", Call("Dvd", V("a"), Sub(V("P"), D(1))),
                    All("hP", LT(D(0), V("P")),
                        Ex("I", Call("Correct", table, Call("proof", LE(D(2), p)), V("hP")), body))))));
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
