using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects;

internal sealed class HardinA203981StripSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripSymmetry.";
    private const string Note = "D5/L/SpinModels/hardin2012a203981";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetries of six-column diagonal bonds", H("Symmetries of six-column diagonal bonds"), Blocks(
        Describe.Lean(DescribeId.Create("cost-formula"), DeclarationHandle.Create(Prefix + "cost_formula"),
            H("Ten diagonal-bond indicators"), StatementSource.FromAuthor(Disp(CostFormula())),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Each pair of adjacent columns supplies one diagonal bond in each orientation."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lift-counts"), DeclarationHandle.Create(Prefix + "lift_counts"),
            H("Transfer counts are constant on a boundary class"), StatementSource.FromAuthor(Disp(All("d", V("Nat"), All("t", Call("Matrix", Fin("15"), Fin("15"), V("Int")), Imp(All("i", Fin("15"), All("j", Fin("15"), Eq(SumOver("r", Row("6"), If(And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), Call("HardinA203981StripData.representatives", V("i")), V("r")), V("d")), Eq(Call("HardinA203981StripData.boundary", V("r")), V("j"))), CastInt(N("1")), CastInt(N("0")))), App(V("t"), V("i"), V("j"))))), All("p", Row("6"), All("j", Fin("15"), Eq(SumOver("r", Row("6"), If(And(Eq(Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), V("p"), V("r")), V("d")), Eq(Call("HardinA203981StripData.boundary", V("r")), V("j"))), CastInt(N("1")), CastInt(N("0")))), App(V("t"), Call("HardinA203981StripData.boundary", V("p")), V("j")))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text("Independent colour permutations on the two parities preserve cost when interchanged on the next row. Reflection exchanges the two triples and preserves cost. HardinA233258PairTransfer supplies the colour invariance and representative of each triple class. The resulting bijections transport each exact-cost sum to its representative."))), DescribeRole.Theorem))));
    private static Formula CostFormula()
    {
        var p = V("p");
        var r = V("r");
        Formula Bond(int i, int j) => If(Eq(App(p, D((byte)i)), App(r, D((byte)j))), N("1"), N("0"));
        var indicators = Enumerable.Range(0, 5).SelectMany(i => new[] { Bond(i, i + 1), Bond(i + 1, i) });
        var cost = indicators.Aggregate((a, b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b));
        return All("p", Row("6"), All("r", Row("6"),
            Eq(Call("DefectTransfer.bondDefects", Call("HardinA229637RowColumn.betw", N("6")), p, r), cost)));
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
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula CastInt(Formula a) => Typed(a, V("Int"));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Fin(string n) => Call("Fin", N(n));
    private static Formula Row(string n) => Arr(Fin(n), Fin("3"));
    private static Formula If(Formula c, Formula y, Formula n) =>
        Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));
}
