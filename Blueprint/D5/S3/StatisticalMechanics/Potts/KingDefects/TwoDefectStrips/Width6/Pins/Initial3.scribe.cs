using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins;
internal sealed class Initial3Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229753");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate identities for width-six king transfers.", H("Width-six transfer identities"), Blocks(Paragraph(Text("This is a domain enumeration of admissible initial rows by class and exact defect budget. Its sum counts labelled rows, and supplies the initial part of the structural transfer certificate.")),
            Describe.Lean(DescribeId.Create("certificate"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Pins/Initial3.certificate"),
                H("Initial3"), StatementSource.FromAuthor(Disp(All("s", Call("Fin", Num("36")), Eq(SumOver("r", Call("Data.Row"), Conditional(And(Leq(Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r")), Num("2")), Eq(Call("Data.cl", V("r"), Sub(Num("2"), Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r")))), Call("Fin.mk", Add(Num("12"), Call("Fin.val", V("s")))))), Num("1"), Num("0"))), Call("Data.initial", Call("Fin.mk", Add(Num("12"), Call("Fin.val", V("s"))))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The accumulated suffix coordinates of the initial class weights equal the exact labelled first-row sums with at most two horizontal defects."))), DescribeRole.Theorem))));

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
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x), t)), Sp, Parenthesized(b));
    private static Formula Conditional(Formula a, Formula b, Formula c) => Parenthesized(Seq(Q("if"), Sp, a, Sp, Q("then"), Sp, b, Sp, Q("else"), Sp, c));

}
