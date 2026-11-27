using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6;

internal sealed class ZeroTemperatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233166");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-column proper-colouring correspondence determines the zero-temperature block.",
        H("Width-six proper successors from the zone owner"),
        Blocks(
            Node("two-rows", "The two-row rectangle", "twoRows",
                "Two six-column rows form a height-two rectangle, with the source first and the successor second.", DescribeRole.Definition),
            Node("raw", "The zero-defect successor relation", "raw",
                "The between-row and target horizontal defect counts both vanish.", DescribeRole.Definition),
            Node("offsets", "The translated row offsets", "offsets",
                "Offsets translate a proper row by its first entry, producing the owner zone word.", DescribeRole.Definition),
            Node("raw-iff-shift", "The exact allowed-shift image", "raw_iff_shift",
                "For a horizontally proper source row, the zero-defect successor rows are exactly the owner offset choices translated across that source. The map sends v to the row j -> v xor p(j); its inverse sends r to r(0) xor p(0). Cancellation gives one successor per allowed shift.", DescribeRole.Theorem),
            Node("transition-counts", "The zero-temperature transfer row", "transition_counts",
                "For every horizontally proper source and every class column, the zero-budget successor sum equals the width-six transfer row computed from the allowed shifts. The horizontal properness assumption is essential; rows whose source already has defects use the defect certificates.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(NodeFormula(declaration))), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula NodeFormula(string declaration) => declaration switch
    {
        "raw" => All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("4"))), All("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("4"))), Iff(Call("raw", V("p"), V("r")), Eq(Add(Call("DefectTransfer.bondDefects", Call("Width6.Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Width6.Data.horizontal"), V("r"), V("r"))), Num("0"))))),
        "raw_iff_shift" => All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("4"))), All("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("4"))), Imp(Eq(Call("DefectTransfer.bondDefects", Call("Width6.Data.horizontal"), V("p"), V("p")), Num("0")), Iff(Call("raw", V("p"), V("r")), Ex("v", Call("Fin", Num("4")), And(Member(V("v"), Call("HardinA233166KingStrip.offsetChoices", Call("offsets", V("p")))), Eq(V("r"), Lam("j", Call("Fin", Num("6")), Call("Fin.xor", V("v"), App(V("p"), V("j"))))))))))),
        "transition_counts" => All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("4"))), Imp(Eq(Call("DefectTransfer.bondDefects", Call("Width6.Data.horizontal"), V("p"), V("p")), Num("0")), All("s", Call("Fin", Num("96")), Eq(SumOver("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("4"))), Conditional(And(Leq(Add(Call("DefectTransfer.bondDefects", Call("Width6.Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Width6.Data.horizontal"), V("r"), V("r"))), Num("0")), Eq(Call("Width6.Data.cl", V("r"), Sub(Num("0"), Add(Call("DefectTransfer.bondDefects", Call("Width6.Data.between"), V("p"), V("r")), Call("DefectTransfer.bondDefects", Call("Width6.Data.horizontal"), V("r"), V("r"))))), V("s"))), Typed(Num("1"), Call("Int")), Typed(Num("0"), Call("Int")))), Call("Width6.Data.T", Call("Width6.Data.cl", V("p"), Num("0")), V("s")))))),
        "twoRows" => All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("4"))), All("r", Arrow(Call("Fin", Num("6")), Call("Fin", Num("4"))), Eq(Call("twoRows", V("p"), V("r")), Lam("ij", Product(Call("Fin", Num("2")), Call("Fin", Num("6"))), Conditional(Eq(Call("Prod.fst", V("ij")), Num("0")), App(V("p"), Call("Prod.snd", V("ij"))), App(V("r"), Call("Prod.snd", V("ij")))))))),
        "offsets" => All("p", Arrow(Call("Fin", Num("6")), Call("Fin", Num("4"))), Eq(Call("offsets", V("p")), Lam("j", Call("Fin", Num("6")), Call("Fin.xor", App(V("p"), Num("0")), App(V("p"), V("j")))))),
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
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Conditional(Formula a, Formula b, Formula c) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(a), Sp, Q("then"), Sp, b, Sp, Q("else"), Sp, c));
    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x),t)), Sp, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ex(string x, Formula t, Formula b) => Seq(Exists, Sp, Typed(V(x),t), Comma, Sp, Parenthesized(b));

}
