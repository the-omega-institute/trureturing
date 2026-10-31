using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtYoungMultiplicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The diagonal and dominance zeros of Young multiplicities", H("The diagonal and dominance zeros of Young multiplicities"), Blocks(
            Paragraph(Text("For a Young diagram D and a partition nu of its number of cells, m(D,nu) is the dimension over the rationals of the actual intertwiner space from the preserved Specht span S(D) to the Young permutation module M(nu). It is zero unless shape(D) dominates nu. On the diagonal, scalar multiplication of the inclusion identifies that intertwiner space with the rationals, giving dimension one. The proof uses the actual column antisymmetrizer, its preimage in the Specht span, and the orbit spanning property of a polytabloid. These results supply the triangular part of Young rule; they do not identify the other entries with Kostka numbers.")),
            Describe.Lean(DescribeId.Create("specht-multiplicity-eq-zero-of-not-dominates"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungMultiplicity.spechtMultiplicity_eq_zero_of_not_dominates"),
                H("The dominance zero region"), StatementSource.FromAuthor(Disp(All("D", Call("YoungDiagram"), All("nu", Part(Call("card", Id("D"))), Imp(Call("Not", Call("Dominates", Call("shape", Id("D")), Id("nu"))), Eq(Call("m", Id("D"), Id("nu")), D(0))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("specht-multiplicity-self"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtYoungMultiplicity.spechtMultiplicity_self"),
                H("The actual diagonal dimension"), StatementSource.FromAuthor(Disp(All("D", Call("YoungDiagram"), Eq(Call("m", Id("D"), Call("shape", Id("D"))), D(1))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation has the meanings specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Part(Formula n) => Call("Partition", n);
}
