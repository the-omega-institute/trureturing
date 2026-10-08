using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ActualControlSlotsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual terminal reading slots identify exactly the original sources of a stationary controller.",
        H("General-base stationary control and actual terminal slots"),
        Blocks(
            Paragraph(Text(
                "For p at least two and positive P, the physical source is ZMod(pP). "
                + "The digit is floor(val/P) in Fin p. A controller has one source-independent "
                + "initial control and fixed total action, wait-successor, digit-row-successor "
                + "and output functions. Its actions partition Q into read, wait and halt. "
                + "A wait increments the source by one; a read preserves it. Halt is absorbing "
                + "in the mathematical trajectory and emits no action.")),
            Paragraph(Text(
                "Correct supplies a finite stop time for every original source, exact fixed "
                + "terminal decoding, and no earlier halt. The initial action is a read, "
                + "consecutive reads have positive waits, and the final action is a read. "
                + "A used slot records an actual read occurrence and digit. It is terminal "
                + "precisely when that fixed digit-row successor is a halt control. "
                + "For p=3 and P greater than one this is the same action semantics as "
                + "StationaryUnitControl: wait(next), read(row), and halt(label) supply the "
                + "three corresponding total functions, and unused table entries are arbitrary.")),
            Describe.Lean(DescribeId.Create("actual-control-terminal-slots"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/ActualControlSlots.result"),
                H("Terminal slots and nonreturn of the common start"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each original source supplies its final read slot. A used terminal slot "
                    + "must be that source's final read, since its fixed successor halts. "
                    + "Fixed terminal decoding makes this correspondence bijective. Equal "
                    + "joint configurations force equal original sources and event times; "
                    + "because initial sources cover every physical value, the initial "
                    + "reading control has no later occurrence. Reading controls may "
                    + "otherwise recur or merge. No directed next-read graph or capacity "
                    + "inequality is asserted here."))), DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var run = Call("run", V("C"), V("hp"), V("hP"), V("x"), V("t"));
        var slots = Seq(OpenBrace, V("s"), Colon,
            Seq(V("Q"), Times, Sp, Call("Fin", V("p"))), Vert, Sp,
            Call("Terminal", V("C"), V("I"), Call("fst", V("s")), Call("snd", V("s"))), CloseBrace);
        var body = And(EqF(Call("NatCard", slots), Mul(V("p"), V("P"))),
            All("x", Source, All("t", N, Imp(LE(V("t"), Call("length", V("I"), V("x"))),
                Imp(EqF(Call("snd", run), Call("initial", V("C"))), EqF(V("t"), D(0)))))));
        return All("p", N, All("P", N, All("Q", V("Type"),
            All("hp", LE(D(2), V("p")), All("hP", LT(D(0), V("P")),
            All("C", Call("Controller", V("p"), V("P"), V("Q")),
            All("I", Call("Correct", V("C"), V("hp"), V("hP")),
                body))))))));
    }
    private static Formula V(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Source => Call("ZMod", Mul(V("p"), V("P")));
    private static Formula Mul(Formula a, Formula b) => Seq(Grp(a), Times, Sp, Grp(b));
    private static Formula EqF(Formula a, Formula b) => Seq(Grp(a), Eq, Grp(b));
    private static Formula LE(Formula a, Formula b) => Seq(Grp(a), Le, Sp, Grp(b));
    private static Formula LT(Formula a, Formula b) => Seq(Grp(a), Lt, Grp(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula And(Formula a, Formula b) => Seq(Grp(a), Land, Grp(b));
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, type, Comma, Grp(body));
    private static Formula Call(string s, params Formula[] args) => Seq(
        Operatorname, Sp, Grp(V(s)), Open,
        Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x })]), Close);
}
