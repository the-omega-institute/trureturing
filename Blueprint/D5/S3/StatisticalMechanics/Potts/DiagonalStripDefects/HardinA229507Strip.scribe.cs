using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;
internal sealed class HardinA229507StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507Strip.";
    private const string Note = "D5/L/SpinModels/hardin2013a229507";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-budget diagonal and antidiagonal arrays.", H("Five-column strip colourings"), Blocks(
        Describe.Lean(DescribeId.Create("d0"), DeclarationHandle.Create(Prefix + "a"), H("a"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA229507Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("f", Arrow(Product(Call("Fin", V("n")), Fin(5)), Fin(3)), And(Eq(Call("DefectTransfer.defects", Call("HardinA203980StripData.horizontal"), Call("HardinA203980StripData.between"), Call("List.ofFn", Fn("i", Call("Fin", V("n")), Fn("j", Fin(5), App(V("f"), Pair(V("i"), V("j"))))))), Num("1")), All("p", Product(Call("Fin", V("n")), Fin(5)), All("c", Fin(3), Imp(Lt(V("c"), App(V("f"), V("p"))), Ex("q", Product(Call("Fin", V("n")), Fin(5)), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("5")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("5")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("f"), V("q")), V("c"))))))))), Call("Finset.univ"))))))), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The filtered count uses n rows and five columns, exactly 1 diagonal or antidiagonal equal-colour bonds, and the original row-major colour introduction predicate. The ordinal 5*i+j orders the cells."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d1"), DeclarationHandle.Create(Prefix + "counting_bridge"), H("counting_bridge"), StatementSource.FromAuthor(Disp(All("m", V("Nat"), Eq(Call("dotProduct", Call("HardinA229507StripData.initial"), Call("Matrix.mulVec", new Formula.Power(Call("HardinA229507StripData.T"), V("m")), Call("HardinA229507StripData.terminal"))), Mul(Num("6"), CastInt(Call("HardinA229507Strip.a", Add(V("m"), Num("1"))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("Constant arrays have 8*m equal-colour bonds, so exactly 1 defects excludes them. Every canonical array therefore has exactly six labelled realizations."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("d2"), DeclarationHandle.Create(Prefix + "result"), H("result"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("HardinA229507Strip.a", Add(V("n"), Num("10")))), Sub(Add(Sub(Sub(Add(Sub(Sub(Mul(Num("30"), CastInt(Call("HardinA229507Strip.a", Add(V("n"), Num("9"))))), Mul(Num("225"), CastInt(Call("HardinA229507Strip.a", Add(V("n"), Num("8")))))), Mul(Num("540"), CastInt(Call("HardinA229507Strip.a", Add(V("n"), Num("7")))))), Mul(Num("8748"), CastInt(Call("HardinA229507Strip.a", Add(V("n"), Num("6")))))), Mul(Num("9720"), CastInt(Call("HardinA229507Strip.a", Add(V("n"), Num("5")))))), Mul(Num("72900"), CastInt(Call("HardinA229507Strip.a", Add(V("n"), Num("4")))))), Mul(Num("174960"), CastInt(Call("HardinA229507Strip.a", Add(V("n"), Num("3")))))), Mul(Num("104976"), CastInt(Call("HardinA229507Strip.a", Add(V("n"), Num("2")))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The finite vector relation propagates to every later power. The canonical counting bridge gives the recurrence at every index at least 10."))), DescribeRole.Theorem))));
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Fn(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, V(n), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(b));

    private static Formula Fin(int n) => Call("Fin", Num(n.ToString(System.Globalization.CultureInfo.InvariantCulture)));
}
