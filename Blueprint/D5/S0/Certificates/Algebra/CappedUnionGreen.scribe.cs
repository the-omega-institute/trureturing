using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class CappedUnionGreenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Algebra/CappedUnionGreen.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Semigroups/mazhang2026wangcounterexamples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In the capped union monoid every principal ideal is a coordinate up-set, so Green H is equality and every Schutzenberger group is trivial.",
        H("Principal ideals and Green classes of the capped union monoid"),
        Blocks(
            Describe.Lean(DescribeId.Create("capped-green-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Lemma 3"), StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every a=(A,k) in S_U: the principal ideal {a} union (a+S_U) of WangConjecture326Refutation.principalIdeal is {(B,j) : A subset of B, k<=j}; Green H in the sense of WangConjecture53Refutation.Green, and the Green congruence WangConjecture326Refutation.greenCon, relate a only to itself; and the translation group Gamma(H_a) of WangConjecture53Refutation, the maps of H_a realized by adding an element of S_U, has exactly one element. Proof: addition only enlarges the support and raises the capped level, and if A is contained in B and k<=j then (A,k)+(B,j-k)=(B,j). Equal ideals therefore force mutual inclusion of supports and mutual inequality of levels, so every H-class is the singleton {a}; the only self-map of a singleton is realized by adding (empty,0). This is Lemma 3 of Ma and Zhang, Zenodo 10.5281/zenodo.23884901, for every set U including the empty one, every k and the identity (empty,0)."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var ideal = Equal(Call("principalIdeal", a),
            Seq(Open, F.Id("x"), Colon, Sp, And(Call("subset", Call("support", a), Call("support", F.Id("x"))),
                Le(Call("level", a), Call("level", F.Id("x")))), Close));
        var green = All("b", Call("Capped", F.Id("U")), Iff(Call("Green", a, b), Equal(a, b)));
        var cong = All("b", Call("Capped", F.Id("U")), Iff(Call("greenCon", a, b), Equal(a, b)));
        var gamma = Call("Unique", Call("Gamma", a));
        return Disp(All("a", Call("Capped", F.Id("U")), And(ideal, And(green, And(cong, gamma)))));
    }

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
