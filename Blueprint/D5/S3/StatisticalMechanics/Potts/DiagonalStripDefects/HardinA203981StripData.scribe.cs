using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;

internal sealed class HardinA203981StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData.";
    private const string Note = "D5/L/SpinModels/hardin2012a203981";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-column boundary classes", H("Six-column boundary classes"), Blocks(
        Describe.Lean(DescribeId.Create("between-six"), DeclarationHandle.Create(Prefix + "between_six"),
            H("Diagonal and antidiagonal bonds"), StatementSource.FromAuthor(Disp(BetweenSixFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Each pair lists the upper and lower column indices of a bond. HardinA229635Literal.same_between identifies the width-six bond set with the union whose pairs are listed here."))), DescribeRole.Theorem),
        Define("column-rows", "Column as a three-position row", ColumnRowsFormula(),
            "The inverse reads a triple of entries from the three positions.", "columnRows"),
        Define("parity-rows", "Parity triples", ParityRowsFormula(),
            "The two triples read the even columns from the left and the odd columns from the right. The inverse interleaves the triples in column order.", "parityRows"),
        Define("pair-class", "Pair of triple patterns", PairClassFormula(),
            "The entry in row a and column b is the index of the unordered pair of triple classes.", "pairClass"),
        Define("boundary", "Boundary class", All("p", Row("6"),
            Eq(Own("boundary", V("p")), Own("pairClass",
                Owner("cls", Fst(Own("parityRows", V("p")))), Owner("cls", Snd(Own("parityRows", V("p"))))))),
            "The boundary index combines the equality classes of the two parity triples."),
        Define("class-pair", "Sorted triple-class pairs", Eq(Typed(Own("classPair"), Arr(Fin("15"),
            Product(Fin("5"), Fin("5")))), Vec(PairNum(0,0), PairNum(0,1), PairNum(0,2), PairNum(0,3),
                PairNum(0,4), PairNum(1,1), PairNum(1,2), PairNum(1,3), PairNum(1,4), PairNum(2,2),
                PairNum(2,3), PairNum(2,4), PairNum(3,3), PairNum(3,4), PairNum(4,4))),
            "The two entries are in increasing order with equality allowed.", "classPair"),
        Define("representatives", "Representative rows", All("i", Fin("15"),
            Eq(Own("representatives", V("i")), App(Call("Equiv.symm", Own("parityRows")),
                Pair(Owner("representatives", Fst(Own("classPair", V("i")))),
                    Owner("representatives", Snd(Own("classPair", V("i")))))))),
            "Each row interleaves two representatives of the three-position equality classes."),
        Define("unordered", "Unordered pair weights", UnorderedFormula(),
            "Equal classes contribute once. Distinct classes contribute in both orders."),
        Define("half-zero", "Zero-cost half-strip block", All("i", Fin("5"), All("j", Fin("5"),
            Eq(Own("halfZero", V("i"), V("j")), Owner("Q", V("i"), Call("Equiv.swap", N("1"), N("3"), V("j")))))),
            "The half-strip reads the target triple backwards, which exchanges classes 1 and 3.", "halfZero"),
        Define("class-product", "Product of two class transitions", ClassProductFormula(),
            "The first and second source classes select the two rows whose target weights are combined.", "classProduct"),
        Define("t", "Zero-cost transfer", Eq(Own("T"), Own("classProduct", Own("halfZero"), Own("halfZero"))),
            "Each parity class contributes its zero-cost transition.", "T"),
        Define("half-initial", "Initial half-strip populations",
            All("i", Fin("5"), Eq(Own("halfInitial", V("i")),
                Call("HardinA229588Strip.initial", Call("Fin.castAdd", N("5"), V("i"))))),
            "The first five entries of the half-strip initial vector are its class populations.", "halfInitial"),
        Define("initial", "Labelled first-row distribution",
            Eq(Own("initial"), Own("unordered", Own("halfInitial"), Own("halfInitial"))),
            "The two independent labelled triples contribute the product of their populations."))));
    private static DocumentBlock Define(string id, string title, Formula formula, string explanation,
        string? declaration = null) =>
        Describe.Lean(DescribeId.Create(id.ToLowerInvariant()), DeclarationHandle.Create(Prefix + (declaration ?? id)),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static Formula Own(string name, params Formula[] xs) => Call("HardinA203981StripData." + name, xs);
    private static Formula Owner(string name, params Formula[] xs) => Call("HardinA233258PairTransfer." + name, xs);
    private static Formula Fst(Formula x) => Call("Prod.fst", x);
    private static Formula Snd(Formula x) => Call("Prod.snd", x);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula PairNum(int a, int b) => Pair(D((byte)a), D((byte)b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));

    private static Formula ParityRowsFormula()
    {
        var p = V("p");
        var t = V("t");
        Formula At(string i) => App(p, N(i));
        var forward = All("p", Row("6"), Eq(Own("parityRows", p),
            Pair(Pair(At("0"), Pair(At("2"), At("4"))), Pair(At("5"), Pair(At("3"), At("1"))))));
        var inverse = All("t", Product(Owner("Col"), Owner("Col")),
            Eq(App(Call("Equiv.symm", Own("parityRows")), t),
                Vec(Fst(Fst(t)), Snd(Snd(Snd(t))), Fst(Snd(Fst(t))), Fst(Snd(Snd(t))),
                    Snd(Snd(Fst(t))), Fst(Snd(t)))));
        return Seq(Parenthesized(forward), Sp, Land, Sp, Parenthesized(inverse));
    }

    private static Formula PairClassFormula() => Eq(Typed(Own("pairClass"), Arr(Fin("5"), Arr(Fin("5"), Fin("15")))),
        Vec(Vec(N("0"), N("1"), N("2"), N("3"), N("4")), Vec(N("1"), N("5"), N("6"), N("7"), N("8")),
            Vec(N("2"), N("6"), N("9"), N("10"), N("11")), Vec(N("3"), N("7"), N("10"), N("12"), N("13")),
            Vec(N("4"), N("8"), N("11"), N("13"), N("14"))));

    private static Formula BetweenSixFormula()
    {
        var bonds = new[] { PairNum(0, 1), PairNum(1, 0), PairNum(1, 2), PairNum(2, 1), PairNum(2, 3),
            PairNum(3, 2), PairNum(3, 4), PairNum(4, 3), PairNum(4, 5), PairNum(5, 4) };
        var edges = Seq(new[] { OpenBrace }
            .Concat(bonds.SelectMany((bond, i) => i == 0 ? new[] { bond } : new[] { Comma, Sp, bond }))
            .Append(CloseBrace).ToArray());
        return Eq(Call("HardinA229637RowColumn.betw", N("6")), edges);
    }

    private static Formula ColumnRowsFormula()
    {
        var c = V("c"); var i = V("i");
        var r = V("r");
        var forward = All("c", Owner("Col"), All("i", Fin("3"),
            Eq(Own("columnRows", c, i), Owner("column", c, i))));
        var inverse = All("r", Row("3"), Eq(App(Call("Equiv.symm", Own("columnRows")), r),
            Pair(App(r, N("0")), Pair(App(r, N("1")), App(r, N("2"))))));
        return Seq(Parenthesized(forward), Sp, Land, Sp, Parenthesized(inverse));
    }

    private static Formula UnorderedFormula()
    {
        var u = V("u"); var v = V("v"); var j = V("j");
        var c = Fst(Own("classPair", j)); var d = Snd(Own("classPair", j));
        var row = Arr(Fin("5"), V("Int"));
        Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
        return All("u", row, All("v", row, All("j", Fin("15"),
            Eq(Own("unordered", u, v, j), new Formula.Binary(Mul(App(u, c), App(v, d)),
                FormulaBinaryOperator.Add, If(Eq(c, d), N("0"), Mul(App(u, d), App(v, c))))))));
    }

    private static Formula ClassProductFormula()
    {
        var a = V("A"); var b = V("B"); var i = V("i"); var j = V("j");
        var matrix = Call("Matrix", Fin("5"), Fin("5"), V("Int"));
        return All("A", matrix, All("B", matrix, All("i", Fin("15"), All("j", Fin("15"),
            Eq(Own("classProduct", a, b, i, j),
                Own("unordered", App(a, Fst(Own("classPair", i))), App(b, Snd(Own("classPair", i))), j))))));
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
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fin(string n) => Call("Fin", N(n));
    private static Formula Row(string n) => Arr(Fin(n), Fin("3"));
    private static Formula If(Formula c, Formula y, Formula n) =>
        Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));
    private static Formula Vec(params Formula[] xs) =>
        Seq(new[] { OpenBracket }.Concat(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }))
            .Append(CloseBracket).ToArray());
}
