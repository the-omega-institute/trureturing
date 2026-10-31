using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtSchurAlternantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alternants and homogeneous multiplication", H("Alternants and homogeneous multiplication"), Blocks(
            Paragraph(Text("The alternant for exponents alpha is the determinant of the matrix with entry X(i)^alpha(j). Its coefficient is the signed sum of permutations transporting the exponent vector. For distinct exponents the coefficient at a permuted exponent vector is its sign. Multiplication by a complete homogeneous polynomial adds every weak composition of its degree.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtSchurAlternant.coeff_alternant_of_injective"),
                H("A distinct exponent coefficient"), StatementSource.FromAuthor(Disp(All("sigma", Call("FiniteDecidableType"), All("R", Call("CommRingType"), All("alpha", Call("Function", Id("sigma"), Nat()), Imp(Call("Injective", Id("alpha")), All("pi", Call("Perm", Id("sigma")), Eq(Call("coeff", Call("alternant", Id("sigma"), Id("R"), Id("alpha")), Call("compose", Id("alpha"), Id("pi"))), Call("castSign", Id("R"), Id("pi")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Nat() => Call("Nat");
}
