using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtMonomialCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sorted monomial coordinates for the Frobenius comparison", H("Sorted monomial coordinates for the Frobenius comparison"), Blocks(
            Paragraph(Text("This supplier is part of the natively compiled full ordinary HSW consumer. Apache source selection is from immutable TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported at unchanged repository pins. The audit remains unfinished at issue 24542.")),
            Paragraph(Text("For any finite alphabet sigma, a degree-n exponent d determines the literal partition of its nonzero exponents. The sorted coordinate partWeight records the row lengths of YoungDiagram.ofPartition, with zero padding. The monomial symmetric coefficient is one precisely at that exponent partition. These selected helpers are consumed by SpechtFixedTabloidPowerSum; no semistandard-tableau or Schur polynomial has been introduced by this coordinate definition.")),
            Describe.Lean(DescribeId.Create("coeff-msymm"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtMonomialCoordinates.coeff_msymm"),
                H("Monomial symmetric coefficients"), StatementSource.FromAuthor(Coefficient()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("Necessary source comparison in the full HSW construction. The displayed abbreviations are defined by the narrative above. There is no independent firstfreeze or standalone admission claim; the remaining public-declaration audit is tracked in issue 24542."))),
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
    private static Formula Part(Formula n) => Call("Partition", n);

    private static Formula Coefficient()
    {
        Formula n = Id("n"), sigma = Id("sigma"), r = Id("R"), nu = Id("nu"), d = Id("d"), h = Id("h");
        Formula body = Eq(Call("coeff", Call("msymm", sigma, r, nu), d),
            Call("ifThenElse", Eq(Call("weightPartition", d, h), nu), D(1), D(0)));
        Formula result = All("h", Eq(Call("degree", d), n), body);
        result = All("d", Call("Finsupp", sigma, Nat()), result);
        result = All("nu", Part(n), result);
        result = All("n", Nat(), result);
        result = All("R", Seq(Call("Type"), Star), Seq(Inst("CommSemiring", r), result));
        result = All("sigma", Seq(Call("Type"), Star),
            Seq(Inst("Fintype", sigma), Inst("DecidableEq", sigma), result));
        return Disp(result);
    }

}
