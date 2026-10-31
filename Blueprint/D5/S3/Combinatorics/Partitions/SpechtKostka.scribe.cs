using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtKostkaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semistandard tableau Kostka numbers", H("Semistandard tableau Kostka numbers"), Blocks(
            Paragraph(Text("K(mu,nu) counts semistandard Young tableaux of the literal diagram of mu with content the row lengths of nu. Every entry in row i is at least i. Counting the entries below k proves dominance; equality of the full row content forces the highest-weight tableau. These facts give triangularity and diagonal one, without choosing labels for irreducible representations.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtKostka.kostkaNumber_self"),
                H("The diagonal Kostka number"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("mu", Part(Id("n")), Eq(Call("K", Id("mu"), Id("mu")), new Formula.Number(1)))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("statement-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtKostka.kostkaNumber_eq_zero_of_not_dominates"),
                H("Dominance vanishing"), StatementSource.FromAuthor(Disp(All("n", Nat(), All("mu", Part(Id("n")), All("nu", Part(Id("n")), Imp(Call("notDominates", Id("mu"), Id("nu")), Eq(Call("K", Id("mu"), Id("nu")), new Formula.Number(0)))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Nat() => Call("Nat");
    private static Formula Part(Formula n) => Call("Partition", n);
}
