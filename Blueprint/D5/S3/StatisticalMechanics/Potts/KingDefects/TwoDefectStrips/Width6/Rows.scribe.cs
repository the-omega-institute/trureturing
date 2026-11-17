using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6;
internal sealed class RowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Rows.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229753");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical width-six boundary rows.", H("Canonical row enumeration"), Blocks(Paragraph(Text("The row table and equality-pattern index are data definitions. Reconstruction is the content certificate that every canonical boundary is represented by its selected entry.")),
            Describe.Remark(DescribeId.Create("rows"), DeclarationHandle.Create(Prefix + "rows"),
                H("Canonical rows"), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The type is Fin 187 -> Data.Row. Each entry is a six-position word over Fin 4 in first-appearance order. The reconstruction theorem pins this table's coverage.")))),
            Describe.Remark(DescribeId.Create("row-index"), DeclarationHandle.Create(Prefix + "rowIndex"),
                H("Equality-pattern index"), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The type is Data.Row -> Fin 187. The index depends only on equalities between row positions. Reconstruction identifies its representative for every canonical row.")))),
            Describe.Lean(DescribeId.Create("reconstruction"), DeclarationHandle.Create(Prefix + "reconstruction"),
                H("Canonical reconstruction"), StatementSource.FromAuthor(Disp(
                    All("p", Q("Data.Row"), Imp(Call("Canonical", V("p")),
                        Eq(Call("rows", Call("rowIndex", V("p"))), V("p")))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Canonicality forces the first coordinate to be zero. The remaining five coordinates determine the row, and finite checks partitioned by the next two coordinates identify its equality-pattern representative. This reconstructs every canonical boundary before colour-permutation transport."))), DescribeRole.Theorem))));
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
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));


}
