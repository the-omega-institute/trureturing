using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5;
internal sealed class ForwardDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Forward.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229752");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite data support the literal width-five king-grid recurrence.", H("Two-defect king transfers"),
        Blocks(Paragraph(Text("The initial and terminal certificates establish the domain interpretation of the table. The Krylov identities normalize the resulting integer entries; the combined certificate retains the domain content.")),
            Describe.Lean(DescribeId.Create("structural-certificate"),
                DeclarationHandle.Create(Prefix + "structural_certificate"), H("Acceptance, initialization and the forward relation"),
                StatementSource.FromAuthor(Disp(And(All("p", Call("Data.Row"), All("d", Call("Fin", Num("3")), Imp(Call("Data.Valid", V("p"), Call("Fin.val", V("d"))), Eq(Call("Data.terminal", Call("Data.cl", V("p"), Call("Fin.val", V("d")))), Conditional(Eq(Call("Fin.val", V("d")), Num("0")), Num("1"), Num("0")))))), And(All("s", Call("Fin", Num("43")), Eq(SumOver("r", Call("Data.Row"), Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r")), Num("2")), Eq(Call("Data.cl", V("r"), Sub(Num("2"), Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r")))), V("s"))), Num("1"), Num("0"))), Call("Data.initial", V("s")))), And(And(Eq(Call("Data.W", Num("0")), Call("Data.initial")), All("i", Call("Fin", Num("11")), Eq(Call("Data.W", Call("Fin.succ", V("i"))), Call("Matrix.vecMul", Call("Data.W", Call("Fin.castSucc", V("i"))), Call("Data.T"))))), Eq(Call("Data.W", Num("11")), SumOver("j", Call("Fin", Num("6")), Call("HSMul.hSMul", App(Call("Matrix.vecCons", Neg(Num("8")), Call("Matrix.vecCons", Num("36"), Call("Matrix.vecCons", Neg(Num("66")), Call("Matrix.vecCons", Num("63"), Call("Matrix.vecCons", Neg(Num("33")), Call("Matrix.vecCons", Num("9"), Call("Matrix.vecEmpty"))))))), V("j")), Call("Data.W", Call("Fin.mk", Add(Num("5"), Call("Fin.val", V("j"))))))))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every valid row and budget, the terminal entry is the zero-budget indicator. The initial vector counts first rows. W(0)=initial and W(i+1)=W(i)T for i=0,...,10. Finally W(11)=-8W(5)+36W(6)-66W(7)+63W(8)-33W(9)+9W(10). Every identity is kernel checked. Terminal, initialization, one-step and annihilation identities are verified separately in finite coordinate groups."))), DescribeRole.Theorem))));

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
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x), t)), Sp, Parenthesized(b));
    private static Formula Conditional(Formula a, Formula b, Formula c) => Parenthesized(Seq(Q("if"), Sp, a, Sp, Q("then"), Sp, b, Sp, Q("else"), Sp, c));
    private static Formula Neg(Formula a) => Seq(Minus, a);

}
