using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtMonomialCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sorted coordinates preserve symmetric coefficients", H("Sorted coordinates preserve symmetric coefficients"), Blocks(
            Paragraph(Text("This supplier is part of the natively compiled full ordinary HSW consumer. Apache source selection is from immutable TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported at unchanged repository pins. The audit remains unfinished at issue 24542.")),
            Paragraph(Text("For a finite alphabet sigma, every exponent d of degree n can be permuted to the sorted coordinate partWeight sigma (weightPartition d h). This coordinate records the literal partition of the nonzero exponents, with zero padding to the alphabet size. A symmetric polynomial has the same coefficient at these two exponents. The fixed-tabloid coefficient calculation consumes this permutation result directly. The unused monomial-symmetric expansion branch is omitted.")),
            Describe.Lean(DescribeId.Create("coeff-eq-coeff-part-weight"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtMonomialCoordinates.coeff_eq_coeff_partWeight"),
                H("Sorted coordinates preserve symmetric coefficients"), StatementSource.FromAuthor(Coefficient()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("This coefficient lemma is consumed in the compiled full ordinary-character HSW proof. There is no independent firstfreeze or standalone admission claim; the remaining public-declaration audit is tracked in issue 24542."))),
                DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Inst(string name, Formula x) => Seq(OpenBracket, Call(name, x), CloseBracket, Comma, Sp);
    private static Formula Nat() => Call("Nat");
    private static Formula Coefficient()
    {
        Formula n = Id("n"), sigma = Id("sigma"), r = Id("R"), p = Id("p"), d = Id("d"), h = Id("h");
        Formula body = Eq(Call("coeff", p, d), Call("coeff", p,
            Call("partWeight", sigma, Call("weightPartition", d, h))));
        Formula result = All("h", Eq(Call("degree", d), n), body);
        result = All("d", Call("Finsupp", sigma, Nat()), result);
        result = All("hp", Call("IsSymmetric", p), result);
        result = All("p", Call("MvPolynomial", sigma, r), result);
        result = All("n", Nat(), result);
        result = All("R", Seq(Call("Type"), Star), Seq(Inst("CommSemiring", r), result));
        result = All("sigma", Seq(Call("Type"), Star),
            Seq(Inst("Fintype", sigma), Inst("DecidableEq", sigma), result));
        return Disp(result);
    }
}
