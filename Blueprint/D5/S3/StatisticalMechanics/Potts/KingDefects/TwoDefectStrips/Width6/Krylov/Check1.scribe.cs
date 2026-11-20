using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Krylov;
internal sealed class Check1Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229753");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate identities for width-six king transfers.", H("Width-six transfer identities"), Blocks(
            Describe.Lean(DescribeId.Create("certificate"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Krylov/Check1.certificate"),
                H("Check1"), StatementSource.FromAuthor(Disp(And(All("i", Call("Fin", Num("11")), All("s", Call("Fin", Num("24")), Eq(Call("Data.W", Call("Fin.succ", V("i")), Call("Fin.mk", Add(Num("0"), Call("Fin.val", V("s"))))), Call("Matrix.vecMul", Call("Data.W", Call("Fin.castSucc", V("i"))), Call("Data.T"), Call("Fin.mk", Add(Num("0"), Call("Fin.val", V("s")))))))), All("s", Call("Fin", Num("24")), Eq(Call("Data.W", Num("11"), Call("Fin.mk", Add(Num("0"), Call("Fin.val", V("s"))))), SumOver("j", Call("Fin", Num("6")), Call("HMul.hMul", App(Call("Matrix.vecCons", Neg(Num("8")), Call("Matrix.vecCons", Num("36"), Call("Matrix.vecCons", Neg(Num("66")), Call("Matrix.vecCons", Num("63"), Call("Matrix.vecCons", Neg(Num("33")), Call("Matrix.vecCons", Num("9"), Call("Matrix.vecEmpty"))))))), V("j")), Call("Data.W", Call("Fin.mk", Add(Num("5"), Call("Fin.val", V("j")))), Call("Fin.mk", Add(Num("0"), Call("Fin.val", V("s")))))))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("At the accumulated prefix coordinates the eleven forward steps follow matrix multiplication, and the order-six polynomial annihilates the shifted forward vectors."))), DescribeRole.Theorem))));

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
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x), t)), Sp, Parenthesized(b));
    private static Formula Neg(Formula a) => Seq(Minus, a);

}
