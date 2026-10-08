using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class SaturatedActualHistoriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A saturated worst-case read bound forces complete physical history trees and distinct reading slots.",
        H("Saturated histories of the original stationary controller"),
        Blocks(
            Paragraph(Text(
                "Use the original Controller and Correct model on ZMod(pP), with p at least "
                + "two, P positive, and an initial read. The action table has fixed read "
                + "successors, fixed wait successors and fixed terminal outputs. The physical "
                + "source stays in the joint run. readEvents(x) is the finite set of actual "
                + "read times before the correct halt. firstFiber(b) is the set of original "
                + "inputs whose initial physical digit is b, and has P elements.")),
            Paragraph(Text(
                "A SaturatedHistory certificate records a complete binary expansion, its "
                + "remaining height, its current slot, its original-input support, and its "
                + "physical read-time function. Every parent-to-child transition is realized "
                + "on that same original input with only actual waits between the two reads. "
                + "The zero time function supplies the first read. Thus the certificate "
                + "describes the existing run and adds no control register or clock.")),
            Paragraph(Text(
                "Write Entry for the dependent sum of remaining height, reading slot, "
                + "finite original-input support, time function and SaturatedHistory "
                + "certificate. entrySlot, entrySupport and entryTime denote its projections. "
                + "historyEntries lists all nodes of one complete actual tree, including "
                + "the first read and terminal reads. allHistories concatenates these trees "
                + "over all first digits, in depth-first order. Its slot list is obtained "
                + "by mapping entrySlot; get indexes this list.")),
            Paragraph(Text(
                "readingPositions lists the pairs of child answer slots at every internal "
                + "history. Each pair is one subsequent reading occurrence. Its two controls "
                + "are equal and its digits are distinct. allReadingPositions concatenates "
                + "these lists over first digits, excluding the initial reads. occurrenceCount "
                + "counts, with multiplicity, the positions assigned to the specified control. "
                + "TerminatesIn counts subsequent reads in the global actual-slot relation "
                + "and retains the fixed terminal label.")),
            Describe.Lean(DescribeId.Create("saturated-actual-history-result"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/SaturatedActualHistories.result"),
                H("Complete histories, slot injection and row packing"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite set of later read times has a least next event whenever the "
                    + "current slot does not halt. Its removal decreases the remaining read "
                    + "count by one. The actual adjacent-slot contract partitions the original "
                    + "support into at most two children. Erasing physical annotations gives "
                    + "a binary adaptive protocol, so the general leaf bound controls support "
                    + "size. Equality at two to the remaining depth excludes empty children "
                    + "and early leaves, producing the complete actual histories. The global "
                    + "slot expansion then fixes each node's remaining height and original "
                    + "support. Ancestors have greater remaining height, sibling subtrees "
                    + "have disjoint supports, and different first digits have disjoint "
                    + "supports. Consequently their slots are distinct across the whole forest. "
                    + "Every physical read event belongs to one of these histories. Each "
                    + "subsequent occurrence occupies two distinct slots of one control; the "
                    + "whole forest has no repeated slot, giving at most floor(p/2) occurrences "
                    + "per control. At P=1 the complete trees have height zero and no such "
                    + "subsequent positions."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var h = V("H");
        var histories = Call("allHistories", V("hp"), V("hP"), V("C"), V("I"), h);
        var slots = Call("map", Seq(Operatorname, Sp, Grp(V("entrySlot"))), histories);
        var positions = Call("allReadingPositions", V("hp"), V("hP"), V("C"), V("I"), h);
        var counts = All("x", Source, EqF(Call("card", Reads(V("x"))), Add(V("D"), D(1))));
        var global = Bind(Seq(Grp(Call("TerminatesIn", V("hp"), V("hP"), V("C"), V("I"),
            V("k"), Pair(V("root"), V("b")), V("x"))), Iff, Grp(And(EqF(V("k"), V("D")),
                EqF(Call("digit", V("hp"), V("hP"), V("x")), V("b"))))),
            ("b", Call("Fin", V("p"))), ("k", N), ("x", Source));
        var injective = Bind(Imp(EqF(Call("get", slots, V("i")), Call("get", slots, V("j"))),
            EqF(V("i"), V("j"))),
            ("i", Call("Fin", Call("length", slots))), ("j", Call("Fin", Call("length", slots))));
        var cover = Bind(Seq(Grp(Member(V("t"), Reads(V("x")))), Iff,
            Grp(Ex("e", Call("Entry", V("hp"), V("hP"), V("C"), V("I")),
                And(Member(V("e"), histories),
                    Member(V("x"), Call("entrySupport", V("e"))),
                    EqF(Call("entryTime", V("e"), V("x")), V("t")))))),
            ("x", Source), ("t", N));
        var packing = All("q", V("Q"), LE(
            Call("occurrenceCount", V("hp"), V("hP"), V("C"), V("I"), h, V("q")),
            Call("div", V("p"), D(2))));
        var forestType = All("b", Call("Fin", V("p")),
            Call("SaturatedHistory", V("hp"), V("hP"), V("C"), V("I"), V("D"),
                Pair(V("root"), V("b")), Call("firstFiber", V("hp"), V("hP"), V("b")),
                Seq(Open, V("x"), Mapsto, Sp, D(0), Close)));
        var conclusions = And(counts, global, injective, cover, packing,
            Imp(EqF(V("P"), D(1)), EqF(positions, Seq(OpenBracket, CloseBracket))));
        var body = Ex("root", ReadsControls, And(
            EqF(Call("val", V("root")), Call("initial", V("C"))), Ex("H", forestType, conclusions)));
        var bound = All("x", Source, LE(Call("card", Reads(V("x"))), Add(V("D"), D(1))));
        body = Imp(EqF(V("P"), Seq(D(2), Caret, Grp(V("D")))), Imp(bound, body));
        body = All("D", N, body);
        body = Seq(OpenBracket, Call("Finite", V("Q")), CloseBracket, Grp(body));
        return Bind(body, ("p", N), ("P", N), ("Q", V("Type")),
            ("hp", LE(D(2), V("p"))), ("hP", Seq(D(0), Lt, V("P"))),
            ("C", Call("Controller", V("p"), V("P"), V("Q"))),
            ("I", Call("Correct", V("C"), V("hp"), V("hP"))));
    }
    private static Formula Reads(Formula x) => Call("readEvents", V("hp"), V("hP"), V("C"), V("I"), x);
    private static Formula ReadsControls => Seq(OpenBrace, V("q"), Colon, V("Q"), Mid, Sp,
        Ex("b", Call("Fin", V("p")), Call("Used", V("C"), V("I"), V("q"), V("b"))), CloseBrace);
    private static Formula Source => Call("ZMod", Seq(V("p"), Times, Sp, V("P")));
    private static Formula Bind(Formula b, params (string Name, Formula Type)[] binders)
    {
        for (var i = binders.Length - 1; i >= 0; i--) b = All(binders[i].Name, binders[i].Type, b);
        return b;
    }
    private static Formula V(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula EqF(Formula a, Formula b) => Seq(Grp(a), Eq, Grp(b));
    private static Formula LE(Formula a, Formula b) => Seq(Grp(a), Le, Sp, Grp(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(Grp(a), Plus, Grp(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, t, Comma, Grp(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, t, Comma, Grp(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Sp, Grp(b));
    private static Formula Join(Formula separator, Formula[] args) =>
        Seq([.. args.SelectMany((x, i) => i == 0
            ? new[] { x } : new[] { separator, x })]);
    private static Formula And(params Formula[] xs) => Join(Land, [.. xs.Select(x => Grp(x))]);
    private static Formula Call(string n, params Formula[] xs) => Seq(Operatorname, Sp, Grp(V(n)), Open, Join(Comma, xs), Close);
}
