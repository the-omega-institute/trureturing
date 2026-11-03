using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class BufferedConeExtensionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/BufferedConeExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite buffered mixed old/new graph retains every old whole path and has one outer-buffer tracer for every new whole path.",
        H("Buffered Whole-Path Retained-Cone Extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("buffered-whole-path-retained-cone"),
                DeclarationHandle.Create(Owner + "buffered_whole_path_extension"),
                H("Finite mixed-buffer graph extension"),
                StatementSource.FromAuthor(FormulaFor()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing")),
                Blocks(
                    Paragraph(Text(
                        "For finite old and new discrete alphabets, closed inner buffers are placed "
                        + "inside old P/C and new D interiors. A compactness transfer cover and the "
                        + "existing finite-open-cover HasShadowing contract produce a finite control "
                        + "cover T.")),
                    Paragraph(Text(
                        "The graph has vertices V×T×B. Its edge relation contains the old edge and "
                        + "one actual point t in X witnessing every old P and new L constraint at "
                        + "both endpoints. The first-coordinate map preserves edges and lifts every "
                        + "specified complete old vertex path, retaining its time-zero vertex.")),
                    Paragraph(Text(
                        "One shadowing tracer serves an entire new path, placing all its iterates in "
                        + "the outer C/D interiors. Conversely, one specified source x lifts every "
                        + "complete old-K/new-L name. This is a fixed finite cone result; it does not "
                        + "supply the global uniform-follower lemma or solve Peng Question 5.1.")),
                    Paragraph(Text(
                        "The four-slot Reg audit for buffered_whole_path_extension remains "
                        + "unfinished. The existing dependent-family owner recipe does not supply "
                        + "this theorem's typed equivalence, variation, sensitivity, observational "
                        + "dependence and exact source-selection evidence. See "
                        + "https://github.com/the-omega-institute/trureturing/issues/25272. "
                        + "No validated registration is claimed."))),
                DescribeRole.Theorem))));

    private static Formula FormulaFor()
    {
        Formula xType = F.Id("X"), aType = F.Id("A"), bType = F.Id("B"), vType = F.Id("V");
        Formula n = F.Id("n"), x = F.Id("x"), z = F.Id("z"), t = F.Id("t");
        Formula a = F.Id("a"), b = F.Id("b"), u = F.Id("u"), v = F.Id("v");
        Formula word = F.Id("w"), cover = F.Id("T");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula vertices = Seq(vType, Sp, Times, Sp, Open, cover, Sp, Times, Sp, bType, Close);
        Formula oldWord = Arr(nat, aType), newWord = Arr(nat, Seq(aType, Sp, Times, Sp, bType));
        Formula oldPath = Arr(nat, vType), newPath = Arr(nat, vertices);
        Formula wn = Call("w", n), un = Part(u, 1), vn = Part(v, 1);
        Formula ub = Part(Part(u, 2), 2), vb = Part(Part(v, 2), 2);
        Formula labels = Seq(u, Sp, Mapsto, Sp, Open, Call("l", un), Comma, Sp, ub, Close);
        Formula language = Call("graphLanguage", F.Id("E"), labels);
        Formula witness = ExistsIn("t", xType, And(
            Mem(t, Part(Part(u, 2), 1)), Mem(t, Call("P", Call("l", un))), Mem(t, Call("L", ub)),
            Mem(Call("f", t), Part(Part(v, 2), 1)),
            Mem(Call("f", t), Call("P", Call("l", vn))), Mem(Call("f", t), Call("L", vb))));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(xType, F.Id("Type")), Comma, Sp,
                Seq(OpenBracket, Call("TopologicalSpace", xType), CloseBracket), Comma, Sp, Seq(OpenBracket, Call("CompactSpace", xType), CloseBracket), Comma, Sp,
                Seq(OpenBracket, Call("T2Space", xType), CloseBracket), Comma),
            Seq(Forall, Sp, Typed(aType, F.Id("Type")), Comma, Sp, Typed(bType, F.Id("Type")), Comma, Sp,
                Seq(OpenBracket, Call("Finite", aType), CloseBracket), Comma, Sp, Seq(OpenBracket, Call("TopologicalSpace", aType), CloseBracket), Comma, Sp,
                Seq(OpenBracket, Call("DiscreteTopology", aType), CloseBracket), Comma, Sp, Seq(OpenBracket, Call("Finite", bType), CloseBracket), Comma, Sp,
                Seq(OpenBracket, Call("TopologicalSpace", bType), CloseBracket), Comma, Sp, Seq(OpenBracket, Call("DiscreteTopology", bType), CloseBracket), Comma),
            Seq(Forall, Sp, Typed(vType, F.Id("Type")), Comma, Sp, Seq(OpenBracket, Call("Finite", vType), CloseBracket), Comma, Sp,
                Typed(F.Id("f"), Arr(xType, xType)), Comma, Sp,
                And(Call("Continuous", F.Id("f")), Call("HasShadowing", F.Id("f"))), Sp, Rightarrow),
            Seq(Forall, Sp, Typed(Seq(F.Id("K"), Comma, F.Id("P"), Comma, F.Id("C")),
                    Arr(aType, Call("Set", xType))), Comma, Sp,
                Typed(Seq(F.Id("L"), Comma, F.Id("D")), Arr(bType, Call("Set", xType))), Comma),
            Seq(All("a", aType, And(Call("IsClosed", Call("K", a)), Call("IsClosed", Call("P", a)),
                Seq(Call("K", a), Sp, Subseteq, Sp, Call("interior", Call("P", a))),
                Seq(Call("P", a), Sp, Subseteq, Sp, Call("interior", Call("C", a))))), Sp, Rightarrow),
            Seq(All("b", bType, And(Call("IsClosed", Call("L", b)),
                Seq(Call("L", b), Sp, Subseteq, Sp, Call("interior", Call("D", b))))), Sp, Rightarrow),
            Seq(And(All("x", xType, ExistsIn("a", aType, Mem(x, Call("interior", Call("K", a))))),
                All("x", xType, ExistsIn("b", bType, Mem(x, Call("interior", Call("L", b)))))), Sp, Rightarrow),
            Seq(Forall, Sp, Typed(F.Id("e"), Arr(vType, Arr(vType, F.Id("Prop")))), Comma, Sp,
                Typed(F.Id("l"), Arr(vType, aType)), Comma),
            Seq(All("v", vType, ExistsIn("p", oldPath, And(
                Seq(Call("p", D(0)), Sp, Eq, Sp, v), Path("e", "p", n, nat)))), Sp, Rightarrow),
            Seq(All("w", oldWord, Seq(Mem(word, Call("graphLanguage", F.Id("e"), F.Id("l"))), Sp,
                Rightarrow, Sp, ExistsIn("x", xType, All("n", nat, Mem(Iterate(n, x), Call("P", wn)))))),
                Sp, Rightarrow),
            Seq(All("x", xType, All("w", oldWord, Seq(
                All("n", nat, Mem(Iterate(n, x), Call("K", wn))), Sp, Rightarrow, Sp,
                Mem(word, Call("graphLanguage", F.Id("e"), F.Id("l")))))), Sp, Rightarrow),
            Seq(Exists, Sp, Typed(cover, Call("Finset", Call("Opens", xType))), Comma, Sp,
                Typed(F.Id("E"), Arr(vertices, Arr(vertices, F.Id("Prop")))), Comma),
            Seq(F.Id("E"), Sp, Eq, Sp, Open, u, Comma, v, Sp, Mapsto, Sp,
                And(Call("e", un, vn), witness), Close, Sp, Land),
            Seq(Call("IsOpenCover", Seq(Open, Typed(F.Id("U"), cover), Close, Sp, Mapsto, Sp, Part(F.Id("U"), 1))), Sp, Land),
            Seq(All("u", vertices, All("v", vertices, Seq(Call("E", u, v), Sp, Rightarrow, Sp,
                Call("e", un, vn)))), Sp, Land),
            Seq(All("p", oldPath, Seq(Path("e", "p", n, nat), Sp, Rightarrow, Sp,
                ExistsIn("r", newPath, And(Path("E", "r", n, nat),
                    All("n", nat, Seq(Part(Call("r", n), 1), Sp, Eq, Sp, Call("p", n))))))), Sp, Land),
            Seq(All("w", newWord, Seq(Mem(word, language), Sp, Rightarrow, Sp,
                ExistsIn("z", xType, All("n", nat, And(
                    Mem(Iterate(n, z), Call("interior", Call("C", Part(wn, 1)))),
                    Mem(Iterate(n, z), Call("interior", Call("D", Part(wn, 2))))))))), Sp, Land),
            All("x", xType, All("w", newWord, Seq(All("n", nat, And(
                Mem(Iterate(n, x), Call("K", Part(wn, 1))), Mem(Iterate(n, x), Call("L", Part(wn, 2))))),
                Sp, Rightarrow, Sp, Mem(word, language))))
        ]));
    }

    private static Formula Arr(Formula from, Formula to) => Seq(from, Sp, Rightarrow, Sp, to);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Mem(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Part(Formula value, byte index) => Seq(Open, value, Close, Dot, D(index));
    private static Formula Iterate(Formula n, Formula x) =>
        Seq(F.Id("f"), Caret, Grp(OpenBracket, n, CloseBracket), Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, Open, Typed(F.Id(name), type), Close, Comma, Sp, Open, body, Close, Close);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, Open, Typed(F.Id(name), type), Close, Comma, Sp, Open, body, Close, Close);
    private static Formula Path(string edge, string path, Formula n, Formula nat) =>
        All("n", nat, Call(edge, Call(path, n), Call(path, Seq(n, Plus, D(1)))));
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var i = 0; i < clauses.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.AddRange([Open, clauses[i], Close]);
        }
        return Seq([.. items]);
    }
}
