using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips;
internal sealed class GridBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229752");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite data support the literal width-five king-grid recurrence.", H("Two-defect king transfers"),
        Blocks(Paragraph(Text("The list-length induction establishes the decomposition of the defect count into row and interface sums. The literal bridge uses that decomposition on its live counting path.")),
            Describe.Lean(DescribeId.Create("defects-rows"),
                DeclarationHandle.Create(Prefix + "defects_rows"), H("Row-list costs as two finite sums"),
                StatementSource.FromAuthor(Disp(All("q", Call("Nat"), All("k", Call("Nat"), All("H", Call("Finset", Cross(Call("Fin", V("k")), Call("Fin", V("k")))), All("V", Call("Finset", Cross(Call("Fin", V("k")), Call("Fin", V("k")))), All("n", Call("Nat"), All("f", Arrow(Call("Fin", Add(V("n"), Num("1"))), Call("DefectTransfer.Row", V("q"), V("k"))), Eq(Call("DefectTransfer.defects", V("H"), V("V"), Call("List.ofFn", V("f"))), Add(SumOver("i", Call("Fin", Add(V("n"), Num("1"))), Call("DefectTransfer.bondDefects", V("H"), Call("f", V("i")), Call("f", V("i")))), SumOver("i", Call("Fin", V("n")), Call("DefectTransfer.bondDefects", V("V"), Call("f", Call("Fin.castSucc", V("i"))), Call("f", Call("Fin.succ", V("i"))))))))))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For arbitrary palette, width, bond sets H and V and n+1 rows, the list cost equals the sum of all n+1 horizontal row costs plus the sum of the n costs between consecutive rows. Induction on n includes the single-row boundary."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-bridge"),
                DeclarationHandle.Create(Prefix + "literal_bridge"), H("The row-list count is the literal labelled grid count"),
                StatementSource.FromAuthor(Disp(All("k", Call("Nat"), All("H", Call("Finset", Cross(Call("Fin", V("k")), Call("Fin", V("k")))), All("V", Call("Finset", Cross(Call("Fin", V("k")), Call("Fin", V("k")))), Imp(All("r", Call("DefectTransfer.Row", Num("4"), V("k")), Eq(Call("DefectTransfer.bondDefects", V("H"), V("r"), V("r")), SumOver("j", Call("Fin", Sub(V("k"), Num("1"))), Conditional(Eq(Call("r", Call("KingGrid.lo", V("j"))), Call("r", Call("KingGrid.hi", V("j")))), Num("1"), Num("0"))))), Imp(All("r", Call("DefectTransfer.Row", Num("4"), V("k")), All("t", Call("DefectTransfer.Row", Num("4"), V("k")), Eq(Call("DefectTransfer.bondDefects", V("V"), V("r"), V("t")), Add(Add(SumOver("j", Call("Fin", V("k")), Conditional(Eq(Call("r", V("j")), Call("t", V("j"))), Num("1"), Num("0"))), SumOver("j", Call("Fin", Sub(V("k"), Num("1"))), Conditional(Eq(Call("r", Call("KingGrid.lo", V("j"))), Call("t", Call("KingGrid.hi", V("j")))), Num("1"), Num("0")))), SumOver("j", Call("Fin", Sub(V("k"), Num("1"))), Conditional(Eq(Call("r", Call("KingGrid.hi", V("j"))), Call("t", Call("KingGrid.lo", V("j")))), Num("1"), Num("0"))))))), All("n", Call("Nat"), Eq(Call("DefectTransfer.literalCount", V("H"), V("V"), Num("2"), Add(V("n"), Num("1"))), Call("KingTwoGrid.L", Add(V("n"), Num("1")), V("k"))))))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Assume H counts adjacent horizontal bonds and V counts the vertical, diagonal and antidiagonal bonds. At every height n+1, the exact two-defect literalCount equals KingTwoGrid.L. KingGrid.sum_edges identifies the four disjoint edge families; the underlying colourings and cell order are identical."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string s)
    {
        var parts = s.Split('_');
        Formula Word(string p) => Seq(p.Select(ch => ch >= '0' && ch <= '9'
            ? Num(new string(new[] { ch })) : V(new string(new[] { ch }))).ToArray());
        Formula result = Word(parts[^1]);
        for (var i = parts.Length - 2; i >= 0; --i)
            result = Seq(Word(parts[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula All(string x, Formula t, Formula b) => Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x), t)), Sp, Parenthesized(b));
    private static Formula Conditional(Formula a, Formula b, Formula c) => Parenthesized(Seq(Q("if"), Sp, a, Sp, Q("then"), Sp, b, Sp, Q("else"), Sp, c));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Cross(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));

}
