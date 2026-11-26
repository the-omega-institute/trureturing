using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;
internal sealed class HardinA203980StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.";
    private const string Note = "D5/L/SpinModels/hardin2012a203980";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-column diagonal and antidiagonal strip counts.", H("Diagonal strip colourings"), Blocks(
        Describe.Lean(DescribeId.Create("d0"), DeclarationHandle.Create(Prefix + "Row"), H("Row"), StatementSource.FromAuthor(Disp(Eq(Call("HardinA203980StripData.Row"), Row()))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("An actual labelled row is a function from Fin 5 to Fin 3."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d1"), DeclarationHandle.Create(Prefix + "horizontal"), H("horizontal"), StatementSource.FromAuthor(Disp(Eq(Parenthesized(Seq(Call("HardinA203980StripData.horizontal"), Colon, Sp, Call("Finset", Call("Prod", Fin(5), Fin(5))))), Call("Finset.empty")))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The within-row bond set is empty."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d2"), DeclarationHandle.Create(Prefix + "between"), H("between"), StatementSource.FromAuthor(Disp(Eq(Parenthesized(Seq(Call("HardinA203980StripData.between"), Colon, Sp, Call("Finset", Call("Prod", Fin(5), Fin(5))))), Call("Finset.insert", Pair(Num("0"), Num("1")), Call("Finset.insert", Pair(Num("1"), Num("0")), Call("Finset.insert", Pair(Num("1"), Num("2")), Call("Finset.insert", Pair(Num("2"), Num("1")), Call("Finset.insert", Pair(Num("2"), Num("3")), Call("Finset.insert", Pair(Num("3"), Num("2")), Call("Finset.insert", Pair(Num("3"), Num("4")), Call("Finset.insert", Pair(Num("4"), Num("3")), Call("Finset.empty")))))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The eight ordered column pairs join adjacent rows diagonally and antidiagonally. No bond joins equal column indices."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d3"), DeclarationHandle.Create(Prefix + "boundary"), H("boundary"), StatementSource.FromAuthor(Disp(All("p", Row(), Eq(Parenthesized(Seq(Call("HardinA203980StripData.boundary", V("p")), Colon, Sp, Fin(8))), Conditional(And(Eq(App(V("p"), Num("0")), App(V("p"), Num("2"))), Eq(App(V("p"), Num("2")), App(V("p"), Num("4")))), Conditional(Eq(App(V("p"), Num("1")), App(V("p"), Num("3"))), Num("0"), Num("1")), Conditional(Eq(App(V("p"), Num("0")), App(V("p"), Num("4"))), Conditional(Eq(App(V("p"), Num("1")), App(V("p"), Num("3"))), Num("2"), Num("3")), Conditional(Or(Eq(App(V("p"), Num("0")), App(V("p"), Num("2"))), Eq(App(V("p"), Num("2")), App(V("p"), Num("4")))), Conditional(Eq(App(V("p"), Num("1")), App(V("p"), Num("3"))), Num("4"), Num("5")), Conditional(Eq(App(V("p"), Num("1")), App(V("p"), Num("3"))), Num("6"), Num("7"))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The eight cases depend on equality among columns zero, two and four and equality between columns one and three. A reflection identifies the two adjacent equality cases."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d4"), DeclarationHandle.Create(Prefix + "representatives"), H("representatives"), StatementSource.FromAuthor(Disp(Parenthesized(Seq(Call("HardinA203980StripData.representatives"), Colon, Sp, Arrow(Fin(8), Row()))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("This table has type Fin 8 to Row, with eight rows of five colours: [[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 0, 2], [0, 0, 1, 1, 2]]. DiagonalSymmetry.lift_counts establishes that these representatives determine successor counts for every actual row."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d5"), DeclarationHandle.Create(Prefix + "T"), H("T"), StatementSource.FromAuthor(Disp(Parenthesized(Seq(Call("HardinA203980StripData.T"), Colon, Sp, Call("Matrix", Fin(8), Fin(8), V("Int")))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The eight by eight integer table is pinned by HardinA203980StripCertificate.counts: entry i,j is the number of cost-zero successors in class j from the representative of class i."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d6"), DeclarationHandle.Create(Prefix + "initial"), H("initial"), StatementSource.FromAuthor(Disp(Parenthesized(Seq(Call("HardinA203980StripData.initial"), Colon, Sp, Arrow(Fin(8), V("Int")))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The eight integer entries are [9, 18, 18, 36, 36, 72, 18, 36]. HardinA203980StripCertificate.initial_counts pins them as the distribution of all 243 labelled rows."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d7"), DeclarationHandle.Create(Prefix + "terminal"), H("terminal"), StatementSource.FromAuthor(Disp(All("j", Fin(8), Eq(App(Call("HardinA203980StripData.terminal"), V("j")), CastInt(Num("1")))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("Each of the eight terminal integer weights is one."))), DescribeRole.Definition))));
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

    private static Formula Fin(int n) => Call("Fin", Num(n.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula Row() => Arrow(Fin(5), Fin(3));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
}
