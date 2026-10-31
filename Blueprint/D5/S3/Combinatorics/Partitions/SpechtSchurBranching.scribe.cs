using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtSchurBranchingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schur branching by the last entry", H("Schur branching by the last entry"), Blocks(
            Paragraph(Text("Restricting a bounded tableau to entries below the last alphabet element gives an interlacing subdiagram. Conversely an interlacing diagram and its tableau determine the extension. This finite bijection proves the branching sum used in the division-free bialternant argument. The interlacingBranchingSum is the sum over nu in interlacingShapes(N,mu) of X(last N)^(card(mu)-card(nu)) times rename(castSucc,diagramSchurPoly(N,R,nu)).")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtSchurBranching.diagramSchurPoly_eq_sum_interlacingShapes"),
                H("Branching expansion"), StatementSource.FromAuthor(Disp(All("N", Nat(), All("R", Call("CommSemiringType"), All("mu", Call("YoungDiagram"), Eq(Call("diagramSchurPoly", Call("succ", Id("N")), Id("R"), Id("mu")), Call("interlacingBranchingSum", Id("N"), Id("R"), Id("mu")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Nat() => Call("Nat");
}
