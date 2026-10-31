using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtFixedTabloidPowerSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power sums and fixed tabloids in arbitrary finite alphabets", H("Power sums and fixed tabloids in arbitrary finite alphabets"), Blocks(
            Paragraph(Text("SOURCE ONLY: no Lean elaboration, accepted axiom closure, proof-term liveness, admission, validated Reg, canonical emission, freeze, deposit, PR or CI result is asserted. Apache source selection is from immutable TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported at unchanged repository pins. The audit remains unfinished at issue 24542.")),
            Paragraph(Text("fixedTabloids(n,nu,pi) means Nat.card of the subtype of left cosets q of the actual Young subgroup youngSubgroup nu satisfying pi smul q = q. It is a count of actual tabloids. psumPart is the existing Mathlib product of power sums, one factor per full partition part including one-cycles. The alphabet is finite but its size may be smaller than n. Every partition of n occurs in the monomial expansion; monomials that do not fit the alphabet contribute zero.")),
            Paragraph(Text("The implementation selects the invariant-colouring expansion, the equivariant coset-to-colouring equivalence, sorted exponent coordinates, and coefficient isolation. It omits the independent averaging formula, the full Schur basis, and every unused companion. The displayed class equality is equality of conjugacy classes under the existing full-partition equivalence.")),
            Describe.Lean(DescribeId.Create("psum-part-eq-sum-card-fixed-points-smul-msymm"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtFixedTabloidPowerSum.psumPart_eq_sum_card_fixedPoints_smul_msymm"),
                H("Fixed-tabloid monomial expansion"), StatementSource.FromAuthor(Expansion()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("Necessary source comparison in the full HSW construction. The displayed abbreviations are defined by the narrative above. There is no independent firstfreeze or standalone admission claim; native liveness and faithful Reg reconstruction remain unchecked."))),
                DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Inst(string name, Formula x) => Seq(OpenBracket, Call(name, x), CloseBracket, Comma, Sp);
    private static Formula Nat() => Call("Nat");
    private static Formula Part(Formula n) => Call("Partition", n);
    private static Formula Perm(Formula n) => Call("Perm", Call("Fin", n));
    private static Formula Count(Formula n, Formula nu, Formula pi) => Call("fixedTabloids", n, nu, pi);

    private static Formula Expansion()
    {
        Formula n = Id("n"), sigma = Id("sigma"), r = Id("R"), rho = Id("rho"), pi = Id("pi"), nu = Id("nu");
        Formula premise = Eq(Call("ConjClassesMk", pi), Call("partitionEquivConjClasses", n, rho));
        Formula body = Eq(Call("psumPart", sigma, r, rho), SumOver("nu", Part(n),
            Smul(Call("natCast", Count(n, nu, pi), r), Call("msymm", sigma, r, nu))));
        return Disp(All("sigma", Seq(Call("Type"), Star), Seq(Inst("Fintype", sigma),
            All("R", Seq(Call("Type"), Star), Seq(Inst("CommSemiring", r), All("n", Nat(),
                All("rho", Part(n), All("pi", Perm(n), Imp(premise, body)))))))));
    }

}
