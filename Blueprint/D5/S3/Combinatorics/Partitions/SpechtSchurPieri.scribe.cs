using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtSchurPieriDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete homogeneous multiplication and horizontal strips", H("Complete homogeneous multiplication and horizontal strips"), Blocks(
            Paragraph(Text("The signed permutation sum cancels exponent vectors outside the interlacing inequalities. The remaining beta-number alternants correspond to horizontal strips. The division-free bialternant identity and injectivity of multiplication by its nonzero factor give Pieri; coefficient transport extends it from integers to every commutative semiring. The horizontalStripSum is the sum of diagramSchurPoly(N,R,ofPartition(lambda)) over every partition lambda of card(mu)+r for which ofPartition(lambda).InterlacedBy(mu).")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtSchurPieri.hsymm_mul_diagramSchurPoly"),
                H("Pieri multiplication"), StatementSource.FromAuthor(Disp(All("N", Nat(), All("R", Call("CommSemiringType"), All("mu", Call("YoungDiagram"), All("r", Nat(), Eq(Mul(Call("hsymm", Id("N"), Id("R"), Id("r")), Call("diagramSchurPoly", Id("N"), Id("R"), Id("mu"))), Call("horizontalStripSum", Id("N"), Id("R"), Id("mu"), Id("r"))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Open, b, Close);
    private static Formula Nat() => Call("Nat");
}
