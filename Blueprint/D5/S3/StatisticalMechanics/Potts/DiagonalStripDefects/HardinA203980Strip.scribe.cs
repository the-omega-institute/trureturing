using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;
internal sealed class HardinA203980StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980Strip.";
    private const string Note = "D5/L/SpinModels/hardin2012a203980";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical diagonal-strip arrays and their recurrence.", H("Five-column zero-defect arrays"), Blocks(
        Describe.Lean(DescribeId.Create("a"), DeclarationHandle.Create(Prefix + "a"), H("Literal canonical arrays"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(Call("HardinA203980Strip.a", V("n")), Call("Finset.card", Call("Finset.filter", Fn("f", Arrow(Product(Call("Fin", Add(V("n"), Num("1"))), Call("Fin", Num("5"))), Call("Fin", Num("3"))), And(Eq(Call("DefectTransfer.defects", Call("HardinA203980StripData.horizontal"), Call("HardinA203980StripData.between"), Call("List.ofFn", Fn("i", Call("Fin", Add(V("n"), Num("1"))), Fn("j", Call("Fin", Num("5")), App(V("f"), Pair(V("i"), V("j"))))))), Num("0")), All("p", Product(Call("Fin", Add(V("n"), Num("1"))), Call("Fin", Num("5"))), All("c", Call("Fin", Num("3")), Imp(Lt(V("c"), App(V("f"), V("p"))), Ex("q", Product(Call("Fin", Add(V("n"), Num("1"))), Call("Fin", Num("5"))), And(Lt(Add(Mul(Call("Fin.val", Call("Prod.fst", V("q"))), Num("5")), Call("Fin.val", Call("Prod.snd", V("q")))), Add(Mul(Call("Fin.val", Call("Prod.fst", V("p"))), Num("5")), Call("Fin.val", Call("Prod.snd", V("p"))))), Eq(App(V("f"), V("q")), V("c"))))))))), Call("Finset.univ"))))))), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The function counts all arrays with n+1 rows and five columns, with no equal-colour diagonal or antidiagonal bond. The order index 5*i+j preserves literal row-major colour introduction."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("counting-bridge"), DeclarationHandle.Create(Prefix + "counting_bridge"), H("Labelled and canonical counts"), StatementSource.FromAuthor(Disp(All("m", V("Nat"), Imp(Leq(Num("1"), V("m")), Eq(Call("dotProduct", Call("HardinA203980StripData.initial"), Call("Matrix.mulVec", new Formula.Power(Call("HardinA203980StripData.T"), V("m")), Call("HardinA203980StripData.terminal"))), Mul(Num("6"), CastInt(Call("HardinA203980Strip.a", V("m"))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("At least two rows supply a bond, so every allowed array uses at least two colours. The permutation action then gives exactly six labelled arrays for each canonical array. The exact-budget transfer and the row-major canonical counting theorem give the identity."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"), H("Order-four recurrence"), StatementSource.FromAuthor(Disp(All("n", V("Nat"), Eq(CastInt(Call("HardinA203980Strip.a", Add(V("n"), Num("5")))), Add(Sub(Mul(Num("15"), CastInt(Call("HardinA203980Strip.a", Add(V("n"), Num("4"))))), Mul(Num("270"), CastInt(Call("HardinA203980Strip.a", Add(V("n"), Num("2")))))), Mul(Num("324"), CastInt(Call("HardinA203980Strip.a", Add(V("n"), Num("1")))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The transfer relation at powers one through five propagates by matrix multiplication. Dividing the labelled counts by six gives the recurrence at every index at least five."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin203980"), ResolutionKind.Proved)))));
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
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
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

}
