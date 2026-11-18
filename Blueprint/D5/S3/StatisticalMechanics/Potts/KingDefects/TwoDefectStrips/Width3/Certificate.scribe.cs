using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width3;
internal sealed class CertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Certificate.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229750");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite data support the literal width-3 king-grid recurrence.", H("Two-defect king transfers"),
        Blocks(Paragraph(Text("The source-class certificates supply new domain transition facts. The canonical reconstruction and permutation transport use those facts to obtain the transfer identity for every labelled source.")),
            Describe.Lean(DescribeId.Create("transition-counts"),
                DeclarationHandle.Create(Prefix + "transition_counts"), H("Exact transfer for every labelled boundary"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA233163KingStrip.Boundary"), All("d", Call("Nat"), Imp(Call("Data.Valid", V("p"), V("d")), All("s", Call("Fin", Num("9")), Eq(SumOver("r", Call("HardinA233163KingStrip.Boundary"), Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r"))), V("d")), Eq(Call("Data.cl", V("r"), Sub(V("d"), Add(Call("DefectTransfer.bondDefects", Call("Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Data.horizontal"), V("r"), V("r"))))), V("s"))), Num("1"), Num("0"))), Call("Data.T", Call("Data.cl", V("p"), V("d")), V("s"))))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every row p, every valid residual budget d and every output class s, the transfer entry is the sum over labelled next rows r with between(p,r)+horizontal(r,r) <= d and residual class s. For proper zero-budget boundaries, the saturated signed certificate of HardinA233163KingStrip supplies the count and class preservation, divided by the constant fibre 8. Canonical existence and colour-permutation reindexing transport the remaining source-class list certificates to arbitrary p."))), DescribeRole.Theorem))));

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

}
