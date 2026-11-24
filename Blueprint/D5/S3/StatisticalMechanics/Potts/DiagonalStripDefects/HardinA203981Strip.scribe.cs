using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;

internal sealed class HardinA203981StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981Strip.";
    private const string Note = "D5/L/SpinModels/hardin2012a203981";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical six-column zero-defect arrays", H("Canonical six-column zero-defect arrays"), Blocks(
        Describe.Lean(DescribeId.Create("a"), DeclarationHandle.Create(Prefix + "a"),
            H("Literal row-major canonical count"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA203981Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("f", Arr(Prod(Call("Fin", Add(V("n"), N("1"))), Fin("6")), Fin("3")), And(Eq(Call("DefectTransfer.defects", Call("Finset.empty"), Call("HardinA229637RowColumn.betw", N("6")), Call("List.ofFn", Fn("i", Call("Fin", Add(V("n"), N("1"))), Fn("j", Fin("6"), App(V("f"), Pair(V("i"), V("j"))))))), N("0")), All("p", Prod(Call("Fin", Add(V("n"), N("1"))), Fin("6")), All("c", Fin("3"), Imp(Lt(V("c"), App(V("f"), V("p"))), Ex("q", Prod(Call("Fin", Add(V("n"), N("1"))), Fin("6")), And(Lt(Add(Mul(N("6"), Call("Fin.val", Call("Prod.fst", V("q")))), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(N("6"), Call("Fin.val", Call("Prod.fst", V("p")))), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("f"), V("q")), V("c"))))))))), Call("Finset.univ"))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The arrays have one more row than the sequence index. The order is the one induced by the row-major index 6i+j, with colours introduced in increasing order. The published sequence starts at index one. The literal filter here also defines index zero."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("scale-count-of-bonds"), DeclarationHandle.Create(Prefix + "scale_count_of_bonds"),
            H("Exact orbit scaling at positive width"), StatementSource.FromAuthor(Disp(ScaleCountOfBondsFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The width is w plus one. H gives the bonds within a row, and V gives the bonds between consecutive rows. A constant array has one copy of H in each row and one copy of V per row pair. At that budget the three constant labelled arrays give one canonical array. Each nonconstant orbit contributes six labellings. Positive width supplies a cell at which to distinguish the three constant arrays."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("scale-count"), DeclarationHandle.Create(Prefix + "scale_count"),
            H("Exact conversion from labelled to canonical arrays"), StatementSource.FromAuthor(Disp(All("m", V("Nat"), All("d", V("Nat"), Eq(Add(App(new Formula.Subscript(Call("DefectTransfer.literalCount"), N("3")), Call("Finset.empty"), Call("HardinA229637RowColumn.betw", N("6")), V("d"), Add(V("m"), N("1"))), Correction(Eq(V("d"), Mul(V("m"), N("10"))))), Mul(N("6"), Call("Finset.card", Call("Finset.filter", Fn("f", Arr(Prod(Call("Fin", Add(V("m"), N("1"))), Fin("6")), Fin("3")), And(Eq(Call("DefectTransfer.defects", Call("Finset.empty"), Call("HardinA229637RowColumn.betw", N("6")), Call("List.ofFn", Fn("i", Call("Fin", Add(V("m"), N("1"))), Fn("j", Fin("6"), App(V("f"), Pair(V("i"), V("j"))))))), V("d")), All("p", Prod(Call("Fin", Add(V("m"), N("1"))), Fin("6")), All("c", Fin("3"), Imp(Lt(V("c"), App(V("f"), V("p"))), Ex("q", Prod(Call("Fin", Add(V("m"), N("1"))), Fin("6")), And(Lt(Add(Mul(N("6"), Call("Fin.val", Call("Prod.fst", V("q")))), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(N("6"), Call("Fin.val", Call("Prod.fst", V("p")))), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("f"), V("q")), V("c"))))))))), Call("Finset.univ"))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The subscript gives the palette size. Each pair of consecutive rows gives ten diagonal and antidiagonal bonds. A constant array with m plus one rows has exactly 10m defects. The constant arrays form one canonical class with three labellings. Every nonconstant class has six labellings."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("counting-bridge"), DeclarationHandle.Create(Prefix + "counting_bridge"),
            H("Exact transfer for the canonical count"), StatementSource.FromAuthor(Disp(All("m", V("Nat"), Eq(Add(Call("dotProduct", Call("HardinA203981StripData.initial"), Call("Matrix.mulVec", Power(Call("HardinA203981StripData.T"), V("m")), Typed(N("1"), Arr(Fin("15"), V("Int"))))), Correction(Eq(V("m"), N("0")))), Mul(N("6"), CastInt(Call("HardinA203981Strip.a", V("m")))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("At least two rows supply a bond, so the zero budget excludes constant arrays and each canonical array has six labelled realizations. A single row admits the constant array, whose orbit has size three."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
            H("Order-six recurrence"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("HardinA203981Strip.a", Add(V("n"), N("7")))), Sub(Add(Add(Sub(Sub(Mul(N("25"), CastInt(Call("HardinA203981Strip.a", Add(V("n"), N("6"))))), Mul(N("45"), CastInt(Call("HardinA203981Strip.a", Add(V("n"), N("5")))))), Mul(N("963"), CastInt(Call("HardinA203981Strip.a", Add(V("n"), N("4")))))), Mul(N("2025"), CastInt(Call("HardinA203981Strip.a", Add(V("n"), N("3")))))), Mul(N("3645"), CastInt(Call("HardinA203981Strip.a", Add(V("n"), N("2")))))), Mul(N("6561"), CastInt(Call("HardinA203981Strip.a", Add(V("n"), N("1")))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("The coefficient relation propagates under additional transfer steps. The displayed shift gives every index at least seven."))), DescribeRole.Theorem))));
    private static Formula ScaleCountOfBondsFormula()
    {
        var w = Add(V("w"), N("1"));
        var m = V("m");
        var height = Add(m, N("1"));
        var rows = Call("Fin", height);
        var columns = Call("Fin", w);
        var cells = Prod(rows, columns);
        var bondSet = Call("Finset", Prod(columns, columns));
        var h = V("H");
        var v = V("V");
        var d = V("d");
        var f = V("f");
        var values = Call("List.ofFn", Fn("i", rows, Fn("j", columns, App(f, Pair(V("i"), V("j"))))));
        Formula Index(Formula cell) => Add(Mul(w, Call("Fin.val", Call("Prod.fst", cell))),
            Call("Fin.val", Call("Prod.snd", cell)));
        var canonical = All("p", cells, All("c", Fin("3"), Imp(Lt(V("c"), App(f, V("p"))),
            Ex("q", cells, And(Lt(Index(V("q")), Index(V("p"))), Eq(App(f, V("q")), V("c")))))));
        var selected = Fn("f", Arr(cells, Fin("3")),
            And(Eq(Call("DefectTransfer.defects", h, v, values), d), canonical));
        var labelled = App(new Formula.Subscript(Call("DefectTransfer.literalCount"), N("3")), h, v, d, height);
        var constantCost = Add(Call("Finset.card", h), Mul(m, Add(Call("Finset.card", v), Call("Finset.card", h))));
        var law = Eq(Add(labelled, Correction(Eq(d, constantCost))),
            Mul(N("6"), Call("Finset.card", Call("Finset.filter", selected, Call("Finset.univ")))));
        return All("w", V("Nat"), All("m", V("Nat"), All("d", V("Nat"), All("H", bondSet, All("V", bondSet, law)))));
    }

    private static Formula N(string digits, bool negative = false) => negative ? Seq(Neg, Sp, N(digits)) :
        D(digits.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part, i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(part))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [..xs]);
    private static Formula Call(string s, params Formula[] xs) => xs.Length == 0 ? Q(s) : App(Q(s), xs);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula x, Formula t) => Parenthesized(Seq(x, Colon, Sp, t));
    private static Formula Arr(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Prod(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Correction(Formula condition) =>
        Parenthesized(Seq(Q("if"), Sp, Parenthesized(condition), Sp, Q("then"), Sp,
            N("3"), Sp, Q("else"), Sp, N("0")));
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula CastInt(Formula a) => Typed(a, V("Int"));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula Fin(string n) => Call("Fin", N(n));
}
