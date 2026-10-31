using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtTableauGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite row coordinates and beta numbers", H("Finite row coordinates and beta numbers"), Blocks(
            Paragraph(Text("A diagram is a finite Young diagram. Its beta number at i is rowLen(i)+N-1-i. The finite row construction uses a decreasing tuple, omits zero rows in its positive row list, and retains those zero rows in its row-length function. Strict decrease of beta numbers gives coefficient isolation for the later alternants.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtTableauGeometry.rowLen_ofRowLensFin"),
                H("Rows of a finite tuple"), StatementSource.FromAuthor(Disp(All("N", Nat(), All("a", Call("Function", Call("Fin", Id("N")), Nat()), Imp(Call("Antitone", Id("a")), All("i", Call("Fin", Id("N")), Eq(Call("rowLen", Call("ofRowLensFin", Id("a")), Id("i")), Call("a", Id("i"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Nat() => Call("Nat");
}
