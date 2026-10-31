using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtSchurTableauxDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tableau Schur polynomials and monomial coordinates", H("Tableau Schur polynomials and monomial coordinates"), Blocks(
            Paragraph(Text("The diagram Schur polynomial is the sum of tableau weight monomials over the finite set of tableaux with entries less than the alphabet size. Transport along Fintype.equivFin defines it for every finite alphabet. Its coefficients are the tableau Kostka numbers. Bender-Knuth symmetry groups them into monomial symmetric polynomials. A diagram taller than the alphabet has no bounded tableau; the degree itself is unrestricted. Here heightExceedsAlphabet means that the number of positive rows exceeds Fintype.card(sigma); nsmul is multiplication by a natural number through repeated addition.")),
            Describe.Lean(DescribeId.Create("statement-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtSchurTableaux.schurPoly_eq_sum_kostkaNumber_smul_msymm"),
                H("Schur monomial expansion"), StatementSource.FromAuthor(Disp(Alphabet(PartAll("mu", Eq(Call("schurPoly", Id("sigma"), Id("R"), Id("mu")), SumOver("nu", Part(Id("n")), Call("nsmul", Call("K", Id("mu"), Id("nu")), Call("msymm", Id("sigma"), Id("R"), Id("nu")))))), "CommSemiring"))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("The notation and hypotheses are specified above."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("statement-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtSchurTableaux.schurPoly_eq_zero_iff"),
                H("Height vanishing"), StatementSource.FromAuthor(Disp(Alphabet(PartAll("mu", Eq(Call("isZero", Call("schurPoly", Id("sigma"), Id("R"), Id("mu"))), Call("heightExceedsAlphabet", Id("mu"), Id("sigma")))), "NontrivialCommSemiring"))),
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
