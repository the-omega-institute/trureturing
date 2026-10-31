using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtFixedTabloidPowerSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power-sum coefficients count actual fixed tabloids", H("Power-sum coefficients count actual fixed tabloids"), Blocks(
            Paragraph(Text("This supplier is part of the natively compiled full ordinary HSW consumer. Apache source selection is from immutable TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported at unchanged repository pins. The audit remains unfinished at issue 24542.")),
            Paragraph(Text("For every finite alphabet sigma and every degree-n exponent d, the coefficient of the full-cycle product psumPart sigma R rho is the count of fixed cosets of the actual Young subgroup of weightPartition d h. Equality of conjugacy classes identifies rho with the full cycle partition of pi, including one-cycles. The coefficient count is cast from the natural numbers into the commutative semiring R. The alphabet size is unrestricted. The invariant-colouring expansion and the equivariant coset-to-colouring equivalence prove this coefficient identity; the full HSW mixed pairing consumes it directly. The unused full monomial-symmetric expansion is omitted.")),
            Describe.Lean(DescribeId.Create("coeff-psum-part-eq-card-fixed-points"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum.coeff_psumPart_eq_card_fixedPoints"),
                H("Power-sum coefficients count actual fixed tabloids"), StatementSource.FromAuthor(Coefficient()),
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
    private static Formula Part(Formula n) => Call("Partition", n);
    private static Formula Coefficient()
    {
        Formula n = Id("n"), sigma = Id("sigma"), r = Id("R"), rho = Id("rho"), pi = Id("pi"), d = Id("d"), h = Id("h");
        Formula body = Eq(Call("coeff", Call("psumPart", sigma, r, rho), d),
            Call("natCast", Call("fixedTabloids", n, Call("weightPartition", d, h), pi), r));
        Formula result = All("h", Eq(Call("degree", d), n), body);
        result = All("d", Call("Finsupp", sigma, Nat()), result);
        result = All("hpi", Eq(Call("ConjClassesMk", pi), Call("partitionEquivConjClasses", n, rho)), result);
        result = All("pi", Call("Perm", Call("Fin", n)), result);
        result = All("rho", Part(n), result);
        result = All("n", Nat(), result);
        result = All("R", Seq(Call("Type"), Star), Seq(Inst("CommSemiring", r), result));
        result = All("sigma", Seq(Call("Type"), Star), Seq(Inst("Fintype", sigma), result));
        return Disp(result);
    }
}
