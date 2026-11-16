using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts;
internal sealed class Check6Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229753");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact multiplicities of successor classes.", H("Width-six class counts"), Blocks(
            Describe.Lean(DescribeId.Create("counts"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Counts/Check6.counts"),
                H("First 84 classes"), StatementSource.FromAuthor(Disp(All("c", Call("Fin", Num("84")), All("s", Call("Fin", Num("96")), Eq(Call("Int.ofNat", Call("List.count", V("s"), Call("Data.classList", Call("Fin.mk", Call("Fin.val", V("c")))))), Call("Data.T", Call("Fin.mk", Call("Fin.val", V("c"))), V("s"))))))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("For each c in Fin 84 and s in Fin 96, the integer cast of the multiplicity of s in classList c equals the matrix entry T(c,s). The source index c is embedded into Fin 96 by its value; Fin.mk omits its bound proof. These cumulative finite checks feed Certificate.transition_counts."))), DescribeRole.Theorem))));

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

}
