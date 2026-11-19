using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0;
internal sealed class Source30Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Chunks0/Source30.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229753");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact successor multisets at canonical boundary states.", H("Width-six source transitions"), Blocks(Paragraph(Text("For the source indices in the displayed range, the sorted list of admissible labelled successors, mapped to their residual-budget classes, equals the class list selected by the source class. Repeated class entries record successor multiplicities.")),
            Describe.Lean(DescribeId.Create("successor-rows"), DeclarationHandle.Create(Prefix + "successor_rows"),
                H("Source states 0 through 200"), StatementSource.FromAuthor(Disp(Formula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "The source table supplies a canonical row and residual budget. Every admissible labelled next row contributes its new class, including multiplicity; sorting gives the class list. These identities determine the quotient transfer."))), DescribeRole.Theorem))));
    private static Formula Formula()
    {
        var x = Call("Sources.sources", Call("Fin.mk", Seq(Num("0"), Plus, Call("Fin.val", V("i")))));
        var p = Call("Prod.fst", x);
        var d = Call("Fin.val", Call("Prod.snd", x));
        return All("i", Call("Fin", Num("201")), Eq(Call("Data.successors", p, d),
            Call("Data.classList", Call("Data.cl", p, d))));
    }
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

}
