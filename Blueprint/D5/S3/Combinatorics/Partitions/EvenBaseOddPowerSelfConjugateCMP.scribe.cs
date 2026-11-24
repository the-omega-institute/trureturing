using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class EvenBaseOddPowerSelfConjugateCMPDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/dietzflowerslockard2026cmp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound for Question 5.12 of Dietz, Flowers and Lockard.",
        H("Odd exponents of even powers with a self-conjugate CMP"),
        Blocks(Describe.Lean(
            DescribeId.Create("dfl512-lower-bound"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/EvenBaseOddPowerSelfConjugateCMP.lower_bound"),
            H("Lower bound on the exponent"),
            StatementSource.FromAuthor(Disp(LowerBound())),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Let L be the first row length and N the number of cells. The first row and first column meet in one cell and the diagram fits in an L by L square, so 2L − 1 ≤ N ≤ L². Since the positive parts are powers of m, write L = m^K. The area bounds and the oddness of e give 0 < 2K − e ≤ e − 2.")),
                Paragraph(Text("The square congruence gives (m − 1)² dividing N − (2L − 1). Expanding the two powers to first order modulo (m − 1)² shows that m − 1 divides 2K − e. This positive multiple is at least m − 1, hence e ≥ m + 1."))),
            DescribeRole.Theorem)), []));

    private static Formula LowerBound()
    {
        Formula m = F.Id("m"), e = F.Id("e"), mu = F.Id("mu");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula hypotheses = Imp(Equal(Call("card", mu), new Formula.Power(m, e)),
            Imp(Call("IsCMP", m, mu), Imp(Equal(Call("transpose", mu), mu),
                AtMost(new Formula.Binary(m, FormulaBinaryOperator.Add, new Formula.Number(1)), e))));
        return All("m", naturals, Imp(AtMost(new Formula.Number(2), m), Imp(Call("Even", m),
            All("e", naturals, Imp(Call("Odd", e), All("mu", Named("YoungDiagram"), hypotheses))))));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, Par(body));
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.Implies, Par(right));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
}
