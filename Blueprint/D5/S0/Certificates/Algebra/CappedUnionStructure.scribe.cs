using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class CappedUnionStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Algebra/CappedUnionStructure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Semigroups/mazhang2026wangcounterexamples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The capped union monoid is periodic, its positive cyclic semigroups are groups exactly off level one, and its algebraic and relative Davenport constants, Green relation and Schutzenberger groups are explicit.",
        H("Structure of the capped union monoid"),
        Blocks(
            Describe.Lean(DescribeId.Create("capped-structure-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Theorem 1"), StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every set U and every nonzero commutative ring R: S_U is periodic in the sense of WangConjecture326Refutation.Periodic, since CappedUnionAlgebraicDavenport.cyclic_le places the positive cyclic subsemigroup of a inside the finite set {a, a+a}. The positive cyclic semigroup of a=(A,k) is a group (WangConjecture326Refutation.CyclicIsGroup) exactly when k is not 1: off level one a+a=a, so the cyclic semigroup is {a} with identity a; at level one an identity e in {a, a+a} would satisfy e+a=a, but a+a and (a+a)+a both have level 2. The remaining clauses are the algebraic Davenport constant algebraicD(S_U,R)=1 (CappedUnionAlgebraicDavenport.result), the Green congruence being equality and the trivial translation groups (CappedUnionGreen.result), and the relative constants D_(A,k)(S_U)=|A|+k (CappedUnionDavenport.result). This is Theorem 1 of Ma and Zhang, Zenodo 10.5281/zenodo.23884901, for arbitrary U; the source's further consequence for U=N, refuting Wang's Conjecture 3.26, is WangConjecture326Refutation.result, proved there on its own copy Model of the same monoid over N; no formal isomorphism between Model and Capped N is stated."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var S = Call("Capped", F.Id("U"));
        var a = F.Id("a");
        var group = All("a", S, Iff(Call("CyclicIsGroup", a), NotEqual(Call("level", a), D(1))));
        var dconst = Equal(Call("algebraicD", S, F.Id("R")), D(1));
        var green = All("a", S, All("b", S, Iff(Call("greenCon", a, F.Id("b")), Equal(a, F.Id("b")))));
        var rel = All("A", Call("Finset", F.Id("U")), All("k", Call("Fin", D(3)),
            Call("IsGreatest", Call("minimalLengths", Call("pair", F.Id("A"), F.Id("k"))), Add(Call("card", F.Id("A")), F.Id("k")))));
        var gamma = All("a", S, Call("Nonempty", Call("Unique", Call("Gamma", a))));
        return Disp(All("R", Call("NontrivialCommRing"), And(Call("Periodic", S), And(group, And(dconst, And(green, And(rel, gamma)))))));
    }

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
}
