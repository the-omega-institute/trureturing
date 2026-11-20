using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5;
internal sealed class Classes38Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Classes38.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229752");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite data support the literal width-five king-grid recurrence.", H("Two-defect king transfers"),
        Blocks(Paragraph(Text("The finite certificate establishes the domain successor multiset and its labelled-row multiplicities. These transition facts supply content for the later transfer proof.")),
            Describe.Lean(DescribeId.Create("class-successors"),
                DeclarationHandle.Create(Prefix + "class_successors"), H("The successor multiset for source class 38"),
                StatementSource.FromAuthor(Disp(All("p", Q("Data.Row"), All("d", Call("Fin", Num("3")), Imp(Call("Data.Valid", V("p"), Call("Fin.val", V("d"))), Imp(Call("Canonical", V("p")), Imp(Eq(Call("Data.cl", V("p"), Call("Fin.val", V("d"))), Num("38")), Eq(Call("Data.successors", V("p"), Call("Fin.val", V("d"))), Call("Data.classList", Num("38")))))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every canonical row and residual budget in this source class, sorting the admissible next-row classes gives the pinned successor list. Multiplicity records distinct labelled rows."))), DescribeRole.Theorem))));
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
