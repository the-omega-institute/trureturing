using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width4;
internal sealed class ZeroTemperatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The proper zero-budget transfer descends from the signed saturated certificate.", H("Complementary-pair fibres"),
        Blocks(Describe.Lean(DescribeId.Create("transition-counts"),
            DeclarationHandle.Create("D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/ZeroTemperature.transition_counts"), H("The zero-budget transfer"),
            StatementSource.FromAuthor(Disp(All("p", Call("HardinA233164KingStrip.Boundary"), Imp(Or(Call("HardinA233164KingStrip.proper", V("p")), Eq(Call("Data.cl", V("p"), Num("0")), Num("14"))), All("s", Call("Fin", Num("19")), Eq(SumOver("r", Call("HardinA233164KingStrip.Boundary"), Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r"))), Num("0")), Eq(Call("Data.cl", V("r"), Sub(Num("0"), Add(Call("DefectTransfer.bondDefects", Call("Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r"))))), V("s"))), Typed(Num("1"), Call("Int")), Typed(Num("0"), Call("Int")))), Call("Data.T", Call("Data.cl", V("p"), Num("0")), V("s")))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229751")),
            Blocks(Paragraph(Text("The map beta sends complementary signed colours to the same four-colour label. Every raw boundary has exactly 16 signed preimages, with two independent choices per column. SignedFibres.sum_beta gives the weighted identity with factor 2^4. The signed row predicate is equivalent to zero defects after applying the map. The owner saturated_certificate preserves the productive boundary type and gives the signed rate. The class containing alternating ABAB also contains ABBA, whose two middle entries coincide. Replacing ABBA by ABAB preserves the zero-defect next-row constraint, and both source rows have class 14. Class correspondence transports kind to the two zero-budget classes, so dividing the signed rate by 16 gives the displayed entry. At width 4, the two signed rates are 32 and 16, hence the raw rates are two and one. All sums and matrix entries are integers; the subtraction inside Data.cl is natural subtraction."))), DescribeRole.Theorem))));

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
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x), t)), Sp, Parenthesized(b));
    private static Formula Conditional(Formula a, Formula b, Formula c) => Parenthesized(Seq(Q("if"), Sp, a, Sp, Q("then"), Sp, b, Sp, Q("else"), Sp, c));

}
