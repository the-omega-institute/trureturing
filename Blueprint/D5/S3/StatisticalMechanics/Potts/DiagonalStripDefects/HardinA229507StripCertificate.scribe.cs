using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;
internal sealed class HardinA229507StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripCertificate.";
    private const string Note = "D5/L/SpinModels/hardin2013a229507";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-budget diagonal and antidiagonal arrays.", H("Five-column strip colourings"), Blocks(
        Describe.Lean(DescribeId.Create("d0"), DeclarationHandle.Create(Prefix + "one_counts"), H("one_counts"), StatementSource.FromAuthor(Disp(All("p", Row(), All("j", Fin(8), Eq(SumOver("r", Row(), CastInt(Conditional(And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA203980StripData.between"), V("p"), V("r")), Num("1")), Eq(Call("HardinA203980StripData.boundary", V("r")), V("j"))), Num("1"), Num("0")))), Call("HardinA229507StripData.costOne", Call("HardinA203980StripData.boundary", V("p")), V("j"))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("Each sum counts actual labelled successor rows in the given target boundary class."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("d1"), DeclarationHandle.Create(Prefix + "transition_counts"), H("transition_counts"), StatementSource.FromAuthor(Disp(All("p", Row(), All("d", Fin(2), All("j", Fin(16), Eq(SumOver("r", Row(), CastInt(Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("HardinA203980StripData.between"), V("p"), V("r")), Call("Fin.val", V("d"))), Eq(Call("HardinA229507StripData.cl", V("r"), Sub(Call("Fin.val", V("d")), Call("DefectTransfer.bondDefects", Call("HardinA203980StripData.between"), V("p"), V("r")))), V("j"))), Num("1"), Num("0")))), Call("HardinA229507StripData.T", Call("HardinA229507StripData.cl", V("p"), Call("Fin.val", V("d"))), V("j")))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("Natural-number subtraction gives the remaining budget. The guard requires the bond cost to be at most the current budget. The lower-budget sectors use the preceding exact transition theorem."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("d2"), DeclarationHandle.Create(Prefix + "W"), H("W"), StatementSource.FromAuthor(Disp(Parenthesized(Seq(Call("HardinA229507StripCertificate.W"), Colon, Sp, Arrow(Fin(14), Arrow(Fin(16), V("Int"))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The fourteen by 16 integer table appends a fourteen by eight leading table to HardinA203980StripCertificate.W. The powers theorem pins every row to the corresponding transfer power on the terminal vector."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("d3"), DeclarationHandle.Create(Prefix + "powers"), H("powers"), StatementSource.FromAuthor(Disp(All("i", Fin(14), Eq(Call("Matrix.mulVec", new Formula.Power(Call("HardinA229507StripData.T"), Call("Fin.val", V("i"))), Call("HardinA229507StripData.terminal")), App(Call("HardinA229507StripCertificate.W"), V("i")))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("Multiplication advances the added coordinates while the retained coordinates use the previous powers theorem."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("d4"), DeclarationHandle.Create(Prefix + "finite_certificate"), H("finite_certificate"), StatementSource.FromAuthor(Disp(Eq(Call("Matrix.mulVec", new Formula.Power(Call("HardinA229507StripData.T"), Num("9")), Call("HardinA229507StripData.terminal")), SumOver("k", Fin(8), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("104976"))), Call("Matrix.vecCons", Num("174960"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("72900"))), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("9720"))), Call("Matrix.vecCons", Num("8748"), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("540"))), Call("Matrix.vecCons", Parenthesized(Seq(Minus, Num("225"))), Call("Matrix.vecCons", Num("30"), Call("Matrix.vecEmpty"))))))))), V("k")), Call("Matrix.mulVec", new Formula.Power(Call("HardinA229507StripData.T"), Add(Num("1"), Call("Fin.val", V("k")))), Call("HardinA229507StripData.terminal"))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The eventual vector relation has order 8. The retained coordinates follow the preceding vector relation multiplied by the zero-cost quartic."))), DescribeRole.Theorem))));
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
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

    private static Formula Fin(int n) => Call("Fin", Num(n.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula Row() => Arrow(Fin(5), Fin(3));
}
