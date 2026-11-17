using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5;

internal sealed class ZeroTemperatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233166");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The width-five proper block is the reflected-column restriction of the frozen width-six owner.",
        H("Width-five proper successors by restriction"),
        Blocks(
            Node("extend", "The reflected-column extension", "extend",
                "A width-five row is extended by reflecting its penultimate column into the sixth column. The new adjacent square reflects the preceding square, so it adds no new inequality.", DescribeRole.Definition),
            Node("raw5", "The width-five zero-defect relation", "raw5",
                "The raw successor relation records zero between-row and horizontal defects for width five.", DescribeRole.Definition),
            Node("proper-extend", "Properness is preserved by extension", "proper_extend",
                "The reflected extension has no horizontal defects exactly when the original width-five row has none.", DescribeRole.Theorem),
            Node("raw-extend", "Raw successors are preserved by extension", "raw_extend",
                "The width-six owner relation on reflected extensions is equivalent to the width-five raw relation.", DescribeRole.Theorem),
            Node("raw-iff-owner", "The restricted owner image", "raw_iff_owner",
                "For every horizontally proper width-five source, every zero-defect successor is the restriction of an owner allowed shift, and every such restriction is a successor. The shift is recovered uniquely as r(0) xor p(0), giving fibre multiplicity one.", DescribeRole.Theorem),
            Node("transition-counts", "The zero-temperature transfer row", "transition_counts",
                "For every horizontally proper width-five source and every class column, the zero-budget successor sum equals the width-five transfer row.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(NodeFormula(declaration))), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula NodeFormula(string declaration) => declaration switch
    {
        "raw5" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), All("r", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Iff(Call("raw5", V("p"), V("r")), Eq(Add(Call("DefectTransfer.bondDefects", Call("Width5.Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("r"), V("r"))), Num("0"))))),
        "raw_iff_owner" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), All("r", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Imp(Eq(Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("p"), V("p")), Num("0")), Iff(Call("raw5", V("p"), V("r")), Ex("v", Call("Fin", Num("4")), And(Member(V("v"), Call("HardinA233166KingStrip.offsetChoices", Call("Width6.ZeroTemperature.offsets", Call("extend", V("p"))))), Eq(V("r"), Lam("j", Call("Fin", Num("5")), Call("Fin.xor", V("v"), App(V("p"), V("j"))))))))))),
        "transition_counts" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Imp(Eq(Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("p"), V("p")), Num("0")), All("s", Call("Fin", Num("43")), Eq(SumOver("r", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("Width5.Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("r"), V("r"))), Num("0")), Eq(Call("Width5.Data.cl", V("r"), Sub(Num("0"), Add(Call("DefectTransfer.bondDefects", Call("Width5.Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("r"), V("r"))))), V("s"))), Typed(Num("1"), Call("Int")), Typed(Num("0"), Call("Int")))), Call("Width5.Data.T", Call("Width5.Data.cl", V("p"), Num("0")), V("s")))))),
        "extend" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Eq(Call("extend", V("p")), Word(App(V("p"), Num("0")), App(V("p"), Num("1")), App(V("p"), Num("2")), App(V("p"), Num("3")), App(V("p"), Num("4")), App(V("p"), Num("3"))))),
        "proper_extend" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Iff(Eq(Call("DefectTransfer.bondDefects", Call("Width6.Data.horizontal"), Call("extend", V("p")), Call("extend", V("p"))), Num("0")), Eq(Call("DefectTransfer.bondDefects", Call("Width5.Data.horizontal"), V("p"), V("p")), Num("0")))),
        "raw_extend" => All("p", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), All("r", Arrow(Call("Fin", Num("5")), Call("Fin", Num("4"))), Iff(Call("Width6.ZeroTemperature.raw", Call("extend", V("p")), Call("extend", V("r"))), Call("raw5", V("p"), V("r"))))),
        _ => throw new System.ArgumentOutOfRangeException(nameof(declaration))
    };

    private static Formula V(string s) => F.Id(s);
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
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Fn(string x, Formula t, Formula b) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(x),t), Sp, Mapsto, Sp, b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Lam(string x, Formula t, Formula b) => Fn(x, t, b);
    private static Formula Word(params Formula[] entries) => Seq(Bang, OpenBracket, Seq(entries.SelectMany((a,i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray()), CloseBracket);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Conditional(Formula a, Formula b, Formula c) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(a), Sp, Q("then"), Sp, b, Sp, Q("else"), Sp, c));
    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x),t)), Sp, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ex(string x, Formula t, Formula b) => Seq(Exists, Sp, Typed(V(x),t), Comma, Sp, Parenthesized(b));

}
