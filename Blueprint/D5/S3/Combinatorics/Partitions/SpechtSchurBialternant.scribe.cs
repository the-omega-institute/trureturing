using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtSchurBialternantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The division-free Schur bialternant identity", H("The division-free Schur bialternant identity"), Blocks(
            Paragraph(Text("For a diagram of height at most N, its tableau Schur polynomial multiplied by the staircase alternant equals the beta-number alternant. Branching proves the identity by induction on N. The identity is an equality of polynomials over any commutative ring and requires no division by a Vandermonde polynomial.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtSchurBialternant.diagramSchurPoly_mul_alternant"),
                H("Division-free bialternant"), StatementSource.FromAuthor(Disp(All("N", Nat(), All("R", Call("CommRingType"), All("mu", Call("YoungDiagram"), Imp(Call("heightLe", Id("mu"), Id("N")), Eq(Mul(Call("diagramSchurPoly", Id("N"), Id("R"), Id("mu")), Call("staircaseAlternant", Id("N"), Id("R"))), Call("betaAlternant", Id("N"), Id("R"), Id("mu"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Open, b, Close);
    private static Formula Nat() => Call("Nat");
}
