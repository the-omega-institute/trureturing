using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;
internal sealed class HardinA203980StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripCertificate.";
    private const string Note = "D5/L/SpinModels/hardin2012a203980";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact diagonal-strip transfer identities.", H("Diagonal strip transfer"), Blocks(
        Describe.Lean(DescribeId.Create("d0"), DeclarationHandle.Create(Prefix + "counts"), H("counts"), StatementSource.FromAuthor(Disp(All("p", Row(), All("j", Fin(8), Eq(SumOver("r", Row(), CastInt(Conditional(And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA203980StripData.between"), V("p"), V("r")), Num("0")), Eq(Call("HardinA203980StripData.boundary", V("r")), V("j"))), Num("1"), Num("0")))), App(Call("HardinA203980StripData.T"), Call("HardinA203980StripData.boundary", V("p")), V("j"))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("For each labelled row and each target class, the successor sum is the corresponding transfer entry. Parity-wise colour permutations and reflection reduce the source to one of eight representatives."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("d1"), DeclarationHandle.Create(Prefix + "initial_counts"), H("initial_counts"), StatementSource.FromAuthor(Disp(All("j", Fin(8), Eq(SumOver("r", Row(), CastInt(Conditional(Eq(Call("HardinA203980StripData.boundary", V("r")), V("j")), Num("1"), Num("0")))), App(Call("HardinA203980StripData.initial"), V("j")))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The sum counts the first rows in each class."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("d2"), DeclarationHandle.Create(Prefix + "W"), H("W"), StatementSource.FromAuthor(Disp(Parenthesized(Seq(Call("HardinA203980StripCertificate.W"), Colon, Sp, Arrow(Fin(14), Arrow(Fin(8), V("Int"))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The fourteen by eight integer table records the zero-cost transfer powers on the all-one vector. HardinA203980StripCertificate.powers pins every coordinate."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d3"), DeclarationHandle.Create(Prefix + "powers"), H("powers"), StatementSource.FromAuthor(Disp(All("i", Fin(14), Eq(Call("Matrix.mulVec", new Formula.Power(Call("HardinA203980StripData.T"), Call("Fin.val", V("i"))), Call("HardinA203980StripData.terminal")), App(Call("HardinA203980StripCertificate.W"), V("i")))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("Every table row is the corresponding transfer power on the terminal vector."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("d4"), DeclarationHandle.Create(Prefix + "finite_certificate"), H("finite_certificate"), StatementSource.FromAuthor(Disp(Eq(Call("Matrix.mulVec", new Formula.Power(Call("HardinA203980StripData.T"), Num("5")), Call("HardinA203980StripData.terminal")), SumOver("j", Fin(4), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Num("324"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("270"))), Call("Matrix.vecCons", Num("0"), Call("Matrix.vecCons", Num("15"), Call("Matrix.vecEmpty"))))), V("j")), Call("Matrix.mulVec", new Formula.Power(Call("HardinA203980StripData.T"), Add(Num("1"), Call("Fin.val", V("j")))), Call("HardinA203980StripData.terminal"))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The fifth power vector is 324 times the first, minus 270 times the second, plus 15 times the fourth."))), DescribeRole.Theorem))));
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
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

    private static Formula Fin(int n) => Call("Fin", Num(n.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula Row() => Arrow(Fin(5), Fin(3));
}
