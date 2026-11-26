using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;
internal sealed class DiagonalSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/DiagonalSymmetry.";
    private const string Note = "D5/L/SpinModels/hardin2012a203980";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact diagonal-strip transfer identities.", H("Diagonal strip transfer"), Blocks(
        Describe.Lean(DescribeId.Create("d0"), DeclarationHandle.Create(Prefix + "lift_counts"), H("lift_counts"), StatementSource.FromAuthor(Disp(All("d", V("Nat"), All("t", Call("Matrix", Fin(8), Fin(8), V("Int")), Imp(All("i", Fin(8), All("j", Fin(8), Eq(SumOver("r", Row(), CastInt(Conditional(And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA203980StripData.between"), App(Call("HardinA203980StripData.representatives"), V("i")), V("r")), V("d")), Eq(Call("HardinA203980StripData.boundary", V("r")), V("j"))), Num("1"), Num("0")))), App(V("t"), V("i"), V("j"))))), All("p", Row(), All("j", Fin(8), Eq(SumOver("r", Row(), CastInt(Conditional(And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA203980StripData.between"), V("p"), V("r")), V("d")), Eq(Call("HardinA203980StripData.boundary", V("r")), V("j"))), Num("1"), Num("0")))), App(V("t"), Call("HardinA203980StripData.boundary", V("p")), V("j")))))))))), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text("The hypothesis fixes the successor count at each representative. Independent permutations on odd and even column indices, with reflection when needed, preserve the inter-row equality count and give a bijection on successor rows. Thus the same matrix counts every labelled source row."))), DescribeRole.Theorem))));
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
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

    private static Formula Fin(int n) => Call("Fin", Num(n.ToString(System.Globalization.CultureInfo.InvariantCulture)));
    private static Formula Row() => Arrow(Fin(5), Fin(3));
}
