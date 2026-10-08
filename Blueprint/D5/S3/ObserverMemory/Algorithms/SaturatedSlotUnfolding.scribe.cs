using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class SaturatedSlotUnfoldingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete actual binary histories determine the global terminal support of their reading slot.",
        H("Saturated actual histories and global slot expansion"),
        Blocks(
            Paragraph(Text(
                "Use the Controller, Correct, Used, Occurs and Edge definitions of ActualControlSlots. "
                + "The physical source is ZMod(pP), with p at least two and P positive. A slot "
                + "is a used reading control together with a digit. Occurs retains the original "
                + "input and its actual event time. Edge joins successive reads on one actual "
                + "input, with only waits in between.")),
            Paragraph(Text(
                "SaturatedHistory(j,u,S,a) is a complete binary history with remaining height j, "
                + "current slot u, original-input support S and actual read-time function a. "
                + "A leaf is the final read on its singleton original input. A fork has two "
                + "distinct child slots, disjoint child supports and histories of equal remaining "
                + "height. For every input in each child support, the parent and child reads "
                + "occur on that same input, in order, with actual waits in between. These "
                + "event times are mathematical indices of the existing run.")),
            Paragraph(Text(
                "TerminatesIn(n,u,x) uses the global actual slot relation. For n=0, the fixed "
                + "successor of u halts with output x. For n+1, an actual slot edge leads to "
                + "a slot that terminates in n. A global path may initially combine edges "
                + "witnessed on different inputs. The theorem identifies all such terminal "
                + "paths with the input support of the complete actual history.")),
            Describe.Lean(DescribeId.Create("actual-read-step"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/SaturatedSlotUnfolding.occurrence_advance"),
                H("A physical read follows its fixed digit row"),
                StatementSource.FromAuthor(Disp(AdvanceStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual reading occurrence at slot u makes the next control "
                    + "equal the fixed row successor of that slot. The source coordinate is unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saturated-history-data"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/SaturatedSlotUnfolding.history_data"),
                H("Original supports and actual event times"),
                StatementSource.FromAuthor(Disp(DataStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The disjoint equal-height children give two to the remaining "
                    + "height original inputs. The support is nonempty, and every supported input "
                    + "actually occurs at the recorded time and slot."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saturated-slot-unfolding"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/SaturatedSlotUnfolding.result"),
                H("Global terminal support and uniqueness at a slot"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two distinct realized child slots exhaust the global successor set, "
                    + "whose cardinality is at most two. Repeating this argument at each child "
                    + "makes every global terminal path have exactly the history's remaining "
                    + "height and a label in its original-input support. Conversely, each such "
                    + "input supplies an actual terminal path. The support has exactly two "
                    + "to the remaining height elements. Hence histories based at the same "
                    + "slot have equal remaining heights and equal supports. This theorem "
                    + "assumes complete actual history certificates; it does not construct "
                    + "them from a controller's worst-case read bound."))),
                DescribeRole.Theorem))));

    private static Formula AdvanceStatement()
    {
        var body = Imp(Call("Occurs", V("C"), V("I"), V("x"), V("t"), V("u")),
            EqF(Call("snd", Call("run", V("C"), V("hp"), V("hP"), V("x"),
                    Seq(V("t"), Plus, D(1)))),
                Call("readNext", V("C"), Call("val", Call("fst", V("u"))), Call("snd", V("u")))));
        return Context(Bind(body, ("x", Source), ("t", N), ("u", Slot)));
    }
    private static Formula DataStatement()
    {
        var body = Imp(Call("Nonempty", History(V("j"), V("u"), V("S"), V("a"))),
            And(EqF(Call("card", V("S")), Seq(D(2), Caret, Grp(V("j")))), Call("Nonempty", V("S")),
                All("x", Source, Imp(Member(V("x"), V("S")),
                    Call("Occurs", V("C"), V("I"), V("x"), Call("a", V("x")), V("u"))))));
        return Context(Bind(body, ("j", N), ("u", Slot), ("S", Call("Finset", Source)),
            ("a", Seq(Source, To, Sp, N))));
    }
    private static Formula Context(Formula body) => Bind(body,
        ("p", N), ("P", N), ("Q", V("Type")), ("hp", Seq(D(2), Le, Sp, V("p"))),
        ("hP", Seq(D(0), Lt, V("P"))), ("C", Call("Controller", V("p"), V("P"), V("Q"))),
        ("I", Call("Correct", V("C"), V("hp"), V("hP"))));
    private static Formula Bind(Formula b, params (string Name, Formula Type)[] binders)
    {
        for (var i = binders.Length - 1; i >= 0; i--) b = All(binders[i].Name, binders[i].Type, b);
        return b;
    }

    private static Formula Statement()
    {
        var j = V("j"); var k = V("k");
        var u = V("u"); var v = V("v");
        var s = V("S"); var t = V("T");
        var path = All("n", N, All("x", Source,
            Seq(Grp(Call("TerminatesIn", V("hp"), V("hP"), V("C"), V("I"),
                    V("n"), u, V("x"))), Iff, Grp(And(EqF(V("n"), j), Member(V("x"), s))))));
        var body = And(path, EqF(Call("card", s), Seq(D(2), Caret, Grp(j))),
            Imp(EqF(u, v), And(EqF(j, k), EqF(s, t))));
        var certificates = Imp(Call("Nonempty", History(j, u, s, V("a"))),
            Imp(Call("Nonempty", History(k, v, t, V("b"))), body));
        return All("p", N, All("P", N, All("Q", V("Type"), Seq(
            OpenBracket, Call("Finite", V("Q")), CloseBracket,
            Grp(All("hp", Seq(D(2), Le, Sp, V("p")),
                All("hP", Seq(D(0), Lt, V("P")),
                All("C", Call("Controller", V("p"), V("P"), V("Q")),
                All("I", Call("Correct", V("C"), V("hp"), V("hP")),
                All("j", N, All("k", N, All("u", Slot, All("v", Slot,
                All("S", Call("Finset", Source), All("T", Call("Finset", Source),
                All("a", Seq(Source, To, Sp, N), All("b", Seq(Source, To, Sp, N),
                    certificates)))))))))))))))));
    }
    private static Formula History(Formula n, Formula u, Formula s, Formula a) =>
        Call("SaturatedHistory", V("hp"), V("hP"), V("C"), V("I"), n, u, s, a);
    private static Formula Source => Call("ZMod", Seq(V("p"), Times, Sp, V("P")));
    private static Formula Slot => Seq(
        OpenBrace, V("q"), Colon, V("Q"), Mid, Sp,
        Ex("d", Call("Fin", V("p")), Call("Used", V("C"), V("I"), V("q"), V("d"))),
        CloseBrace, Times, Sp, Call("Fin", V("p")));
    private static Formula V(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula EqF(Formula a, Formula b) => Seq(Grp(a), Eq, Grp(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, t, Comma, Grp(b));
    private static Formula Ex(string n, Formula t, Formula b) =>
        Seq(Exists, Sp, V(n), Colon, t, Comma, Grp(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Sp, Grp(b));
    private static Formula Join(Formula separator, Formula[] args) =>
        Seq([.. args.SelectMany((x, i) => i == 0
            ? new[] { x } : new[] { separator, x })]);
    private static Formula And(params Formula[] xs) => Join(Land, [.. xs.Select(x => Grp(x))]);
    private static Formula Call(string n, params Formula[] xs) => Seq(
        Operatorname, Sp, Grp(V(n)), Open, Join(Comma, xs), Close);
}
