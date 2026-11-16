using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;
internal sealed class HardinA229691StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229691";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact bond-defect transfer and integer recurrence.", H("Exact defective strip colourings"),
        Blocks(Paragraph(Text("Exactly 2 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.")),
            Describe.Lean(DescribeId.Create("valid"),
                DeclarationHandle.Create(Prefix + "Valid"), H("Residual budgets"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA229583StripData.Boundary"), All("d", V("Nat"), Iff(Call("HardinA229691StripData.Valid", V("p"), V("d")), And(Leq(V("d"), Num("2")), Leq(Call("Finset.card", Call("Finset.filter", Fn("j", Call("Fin", Num("3")), Eq(App(V("p"), Call("Fin.castSucc", V("j"))), App(V("p"), Call("Fin.succ", V("j"))))), Call("Finset.univ"))), Sub(Num("2"), V("d"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The remaining budget is at most the registered exact budget."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("Equality and budget classes"),
                StatementSource.FromAuthor(Disp(ClassifierFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Global colour permutations preserve the equality pattern of the retained column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("T"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229691StripData.T"), Vector(Vector(Num("5"), Num("5"), Num("3"), Num("3"), Num("1"), Num("1"), Num("5"), Num("3"), Num("3"), Num("2"), Num("2"), Num("5"), Num("5"), Num("3"), Num("2"), Num("7"), Num("1"), Num("7"), Num("3"), Num("5"), Num("5"), Num("5"), Num("2"), Num("5"), Num("5"), Num("5"), Num("5")), Vector(Num("4"), Num("4"), Num("3"), Num("3"), Num("2"), Num("2"), Num("4"), Num("2"), Num("2"), Num("3"), Num("3"), Num("6"), Num("6"), Num("3"), Num("0"), Num("7"), Num("2"), Num("7"), Num("2"), Num("8"), Num("8"), Num("5"), Num("3"), Num("5"), Num("5"), Num("5"), Num("6")), Vector(Num("2"), Num("2"), Num("3"), Num("3"), Num("4"), Num("4"), Num("2"), Num("7"), Num("7"), Num("3"), Num("3"), Num("6"), Num("6"), Num("3"), Num("0"), Num("2"), Num("4"), Num("2"), Num("7"), Num("5"), Num("5"), Num("5"), Num("3"), Num("5"), Num("5"), Num("5"), Num("6")), Vector(Num("4"), Num("4"), Num("3"), Num("3"), Num("2"), Num("2"), Num("4"), Num("6"), Num("6"), Num("1"), Num("1"), Num("4"), Num("4"), Num("3"), Num("4"), Num("5"), Num("2"), Num("5"), Num("6"), Num("2"), Num("2"), Num("8"), Num("1"), Num("8"), Num("8"), Num("8"), Num("4")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("1"), Num("0"), Num("1"), Num("3"), Num("7"), Num("7"), Num("1"), Num("0"), Num("1"), Num("7"), Num("7"), Num("2")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("2"), Num("0"), Num("2"), Num("2"), Num("7"), Num("7"), Num("2"), Num("0"), Num("2"), Num("8"), Num("8"), Num("2")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0"), Num("0"), Num("1"), Num("0"), Num("1"), Num("1"), Num("8"), Num("8"), Num("5"), Num("0"), Num("5"), Num("2"), Num("2"), Num("4")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("5"), Num("5"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("1"), Num("0"), Num("1"), Num("5"), Num("3"), Num("3"), Num("2"), Num("0"), Num("2"), Num("5"), Num("5"), Num("3")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("2"), Num("0"), Num("2"), Num("4"), Num("2"), Num("2"), Num("3"), Num("0"), Num("3"), Num("6"), Num("6"), Num("3")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("5"), Num("0"), Num("5"), Num("1"), Num("7"), Num("7"), Num("2"), Num("0"), Num("2"), Num("5"), Num("5"), Num("3")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("4"), Num("0"), Num("4"), Num("2"), Num("5"), Num("5"), Num("1"), Num("0"), Num("1"), Num("4"), Num("4"), Num("3")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("4"), Num("0"), Num("4"), Num("2"), Num("7"), Num("7"), Num("3"), Num("0"), Num("3"), Num("6"), Num("6"), Num("3")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("2"), Num("0"), Num("2"), Num("4"), Num("6"), Num("6"), Num("1"), Num("0"), Num("1"), Num("4"), Num("4"), Num("3")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("2"), Num("0"), Num("2"), Num("2"), Num("5"), Num("5"), Num("4"), Num("0"), Num("4"), Num("8"), Num("8"), Num("2")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("0"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("5"), Num("5"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("4"), Num("4"), Num("0"), Num("0"), Num("0"), Num("3"), Num("3"), Num("0")), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0"), Num("0"), Num("0"), Num("2"), Num("2"), Num("0")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading 14-state block and the ten-state zero-budget submatrix call HardinA229583StripData.T. In the lower sector, shared positions are 1,3,4,5,6,7,9,10,11,12; added positions are 0,2,8. Matrix.fromBlocks and submatrix restore this order. Only added-state interactions remain literal. The other tables give initial weights, terminal acceptance and successive forward weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("initial"),
                DeclarationHandle.Create(Prefix + "initial"), H("initial"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229691StripData.initial"), Vector(Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12"), Num("12"), Num("6"), Num("6"), Num("12"), Num("12"), Num("6"), Num("12"), Num("6"), Num("6"), Num("0"), Num("0"), Num("6"), Num("12"), Num("6"), Num("0"), Num("0"), Num("6"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading 14-state block and the ten-state zero-budget submatrix call HardinA229583StripData.T. In the lower sector, shared positions are 1,3,4,5,6,7,9,10,11,12; added positions are 0,2,8. Matrix.fromBlocks and submatrix restore this order. Only added-state interactions remain literal. The other tables give initial weights, terminal acceptance and successive forward weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("terminal"),
                DeclarationHandle.Create(Prefix + "terminal"), H("terminal"),
                StatementSource.FromAuthor(Disp(Eq(Call("HardinA229691StripData.terminal"), Vector(Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("0"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"), Num("1"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading 14-state block and the ten-state zero-budget submatrix call HardinA229583StripData.T. In the lower sector, shared positions are 1,3,4,5,6,7,9,10,11,12; added positions are 0,2,8. Matrix.fromBlocks and submatrix restore this order. Only added-state interactions remain literal. The other tables give initial weights, terminal acceptance and successive forward weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"),
                DeclarationHandle.Create(Prefix + "W"), H("W"),
                StatementSource.FromAuthor(Disp(ForwardWeightsFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For rows 0 through 5, the leading 14 entries call HardinA229583StripData.W. The appended 13 entries interleave nine new columns with owner columns 4,7,9,11 at positions 2,4,8,12. Rows 6 and 7 are separate literal rows because the owner has only six rows."))), DescribeRole.Definition))));

    private static Formula ForwardWeightsFormula()
    {
        var i = V("i"); var w = V("w"); var v = V("v");
        var newRows = Vector(
            Vector(Num("12"), Num("6"), Num("6"), Num("0"), Num("0"), Num("6"), Num("6"), Num("0"), Num("0")),
            Vector(Num("72"), Num("486"), Num("486"), Num("942"), Num("942"), Num("510"), Num("510"), Num("954"), Num("954")),
            Vector(Num("936"), Num("9702"), Num("9702"), Num("37350"), Num("37350"), Num("10050"), Num("10050"), Num("37278"), Num("37278")),
            Vector(Num("12744"), Num("173070"), Num("173070"), Num("993438"), Num("993438"), Num("179586"), Num("179586"), Num("958446"), Num("958446")),
            Vector(Num("174312"), Num("2913894"), Num("2913894"), Num("22210038"), Num("22210038"), Num("3033018"), Num("3033018"), Num("20838870"), Num("20838870")),
            Vector(Num("2385288"), Num("47327166"), Num("47327166"), Num("449438382"), Num("449438382"), Num("49380354"), Num("49380354"), Num("412458318"), Num("412458318")));
        var finalRows = Vector(
            Vector(Num("87191316"), Num("87191316"), Num("68076936"), Num("68076936"), Num("48962556"), Num("48962556"), Num("87191316"), Num("1116505782"), Num("1116505782"), Num("51756084"), Num("51756084"), Num("961725960"), Num("961725960"), Num("68076936"), Num("32641704"), Num("749602998"), Num("48962556"), Num("749602998"), Num("1116505782"), Num("8519487174"), Num("8519487174"), Num("783513162"), Num("51756084"), Num("783513162"), Num("7681405446"), Num("7681405446"), Num("961725960")),
            Vector(Num("1193183460"), Num("1193183460"), Num("931609512"), Num("931609512"), Num("670035564"), Num("670035564"), Num("1193183460"), Num("17763290766"), Num("17763290766"), Num("708264324"), Num("708264324"), Num("15100570152"), Num("15100570152"), Num("931609512"), Num("446690376"), Num("11653127694"), Num("670035564"), Num("11653127694"), Num("17763290766"), Num("154178657982"), Num("154178657982"), Num("12196766322"), Num("708264324"), Num("12196766322"), Num("137032507998"), Num("137032507998"), Num("15100570152")));
        var row = LetIn("w", Call("HardinA229583StripData.W", i),
            LetIn("v", App(newRows, i), Call("Fin.append", w,
                Vector(App(v, Num("0")), App(v, Num("1")), App(w, Num("4")),
                    App(v, Num("2")), App(w, Num("7")), App(v, Num("3")),
                    App(v, Num("4")), App(v, Num("5")), App(w, Num("9")),
                    App(v, Num("6")), App(v, Num("7")), App(v, Num("8")), App(w, Num("11"))))));
        return Eq(Call("HardinA229691StripData.W"),
            Call("Fin.append", Fn("i", Call("Fin", Num("6")), row), finalRows));
    }

    private static Formula LetIn(string name, Formula value, Formula body) =>
        Seq(Q("let"), Sp, Eq(V(name), value), Sp, Q("in"), Sp, Parenthesized(body));

    private static Formula ClassifierFormula()
    {
        var p = V("p"); var d = V("d");
        var column = Parenthesized(Seq(App(p, Num("0")), Comma, Sp,
            App(p, Num("1")), Comma, Sp, App(p, Num("2")), Comma, Sp,
            App(p, Num("3"))));
        var c = Call("HardinA233177PairTransfer.cls", column);
        Formula Lookup(params int[] entries) => App(Vector(entries.Select(x => Num(x.ToString(System.Globalization.CultureInfo.InvariantCulture))).ToArray()), c);
        return All("p", Call("HardinA229583StripData.Boundary"), All("d", V("Nat"),
            Eq(Call("HardinA229691StripData.cl", p, d),
                Conditional(Eq(d, Num("0")), Lookup(26,14,15,16,17,18,19,20,21,22,23,24,25,26),
                Conditional(Eq(d, Num("1")), Lookup(26,26,4,26,5,6,7,8,9,26,10,11,12,13),
                Conditional(Eq(d, Num("2")), Lookup(26,26,26,26,26,26,0,1,26,26,26,2,3,26),
                    Num("26")))))));
    }

    private static Formula Vector(params Formula[] entries) => Seq(
        new Formula[] { Bang, OpenBracket }.Concat(entries.SelectMany((f, i) =>
            i == 0 ? new[] { f } : new[] { Comma, Sp, f }))
            .Append(CloseBracket).ToArray());
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

}
