using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtTableauInvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bender-Knuth involutions and weights", H("Bender-Knuth involutions and weights"), Blocks(
            Paragraph(Text("The Bender-Knuth involution exchanges the multiplicities of adjacent entries while preserving a semistandard tableau and its shape. Here content(T,x) counts cells with entry x, and swap(v,v+1,x) exchanges those two integers. The bounded version gives a bijection between the corresponding finite weight fibres. The Schur polynomial symmetry proof uses this bijection.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtTableauInvolution.content_benderKnuth"),
                H("Swapping adjacent contents"), StatementSource.FromAuthor(Disp(All("mu", Call("YoungDiagram"), All("T", Call("SemistandardYoungTableau", Id("mu")), All("v", Nat(), All("x", Nat(), Eq(Call("content", Call("benderKnuth", Id("T"), Id("v")), Id("x")), Call("content", Id("T"), Call("swap", Id("v"), Call("succ", Id("v")), Id("x")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Nat() => Call("Nat");
}
