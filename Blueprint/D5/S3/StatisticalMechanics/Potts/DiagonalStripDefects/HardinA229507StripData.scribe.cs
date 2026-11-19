using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;
internal sealed class HardinA229507StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.";
    private const string Note = "D5/L/SpinModels/hardin2013a229507";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-budget diagonal and antidiagonal arrays.", H("Five-column strip colourings"), Blocks(
        Describe.Lean(DescribeId.Create("d0"), DeclarationHandle.Create(Prefix + "cl"), H("cl"), StatementSource.FromAuthor(Disp(All("p", Row(), All("d", V("Nat"), Eq(Parenthesized(Seq(Call("HardinA229507StripData.cl", V("p"), V("d")), Colon, Sp, Fin(16))), Conditional(Lt(Num("0"), V("d")), Call("Fin.castAdd", Num("8"), Call("HardinA203980StripData.boundary", V("p"))), Call("Fin.natAdd", Num("8"), Call("HardinA203980StripData.boundary", V("p"))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The residual budget selects the new leading sector or the retained lower-budget sectors. Fin.castAdd preserves the index value in a larger finite type; Fin.natAdd adds its stated offset to the index value."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d1"), DeclarationHandle.Create(Prefix + "costOne"), H("costOne"), StatementSource.FromAuthor(Disp(Parenthesized(Seq(Call("HardinA229507StripData.costOne"), Colon, Sp, Call("Matrix", Fin(8), Fin(8), V("Int")))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("This eight by eight integer table is pinned by HardinA229507StripCertificate.one_counts: its entries count successors with exactly 1 equal-colour bonds."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d2"), DeclarationHandle.Create(Prefix + "T"), H("T"), StatementSource.FromAuthor(Disp(Eq(Parenthesized(Seq(Call("HardinA229507StripData.T"), Colon, Sp, Call("Matrix", Fin(16), Fin(16), V("Int")))), Call("Matrix.reindex", Parenthesized(Seq(Call("finSumFinEquiv"), Colon, Sp, Call("Equiv", Call("Sum", Fin(8), Fin(8)), Fin(16)))), Parenthesized(Seq(Call("finSumFinEquiv"), Colon, Sp, Call("Equiv", Call("Sum", Fin(8), Fin(8)), Fin(16)))), Call("Matrix.fromBlocks", Call("HardinA203980StripData.T"), Call("HardinA229507StripData.costOne"), Parenthesized(Seq(Num("0"), Colon, Sp, Call("Matrix", Fin(8), Fin(8), V("Int")))), Call("HardinA203980StripData.T")))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The bottom-right 8 by 8 block is HardinA203980StripData.T. The leading sector uses the original zero-cost transfer and the additional exact-cost matrices."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d3"), DeclarationHandle.Create(Prefix + "initial"), H("initial"), StatementSource.FromAuthor(Disp(Eq(Call("HardinA229507StripData.initial"), Call("Fin.append", Call("HardinA203980StripData.initial"), Parenthesized(Seq(Num("0"), Colon, Sp, Arrow(Fin(8), V("Int")))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("All first rows begin in the largest residual budget."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d4"), DeclarationHandle.Create(Prefix + "terminal"), H("terminal"), StatementSource.FromAuthor(Disp(Eq(Call("HardinA229507StripData.terminal"), Call("Fin.append", Parenthesized(Seq(Num("0"), Colon, Sp, Arrow(Fin(8), V("Int")))), Call("HardinA203980StripData.terminal"))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("Acceptance requires the residual budget to be zero."))), DescribeRole.Definition))));
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

    private static Formula Fin(int n) => Call("Fin", Num(n.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula Row() => Arrow(Fin(5), Fin(3));
}
