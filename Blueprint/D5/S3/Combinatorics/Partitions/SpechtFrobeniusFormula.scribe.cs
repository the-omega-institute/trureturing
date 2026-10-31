using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtFrobeniusFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frobenius in every degree and finite alphabet", H("Frobenius in every degree and finite alphabet"), Blocks(
            Paragraph(Text("For every degree n, finite alphabet sigma and commutative ring R, the power-sum product for rho expands in tableau Schur polynomials with the integer ordinary Specht character values of the same partitions. A full-cycle-partition representative and the fixed-tabloid monomial expansion reduce the equality to actual Young rule. This proof uses no inequality between n and the alphabet cardinality; diagrams exceeding its height vanish.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtFrobeniusFormula.psumPart_eq_sum_spechtCharValue_smul_schurPoly"),
                H("Unrestricted finite-alphabet Frobenius formula"), StatementSource.FromAuthor(Disp(Alphabet(PartAll("rho", Eq(Call("psumPart", Id("sigma"), Id("R"), Id("rho")), SumOver("mu", Part(Id("n")), Call("zsmul", Call("spechtCharValue", Id("mu"), Id("rho")), Call("schurPoly", Id("sigma"), Id("R"), Id("mu")))))), "CommRing"))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, Sp, type)), Sp, Open, body, Close);
    private static Formula Nat() => Call("Nat");
    private static Formula Part(Formula n) => Call("Partition", n);
    private static Formula PartAll(string name, Formula body) => All("n", Nat(), All(name, Part(Id("n")), body));
    private static Formula Alphabet(Formula body, string ring) => All("sigma", Call("FiniteType"), All("R", Call(ring + "Type"), body));
}
