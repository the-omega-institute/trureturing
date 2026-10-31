using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtFrobeniusPairingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary Specht traces and Young permutation multiplicities", H("Ordinary Specht traces and Young permutation multiplicities"), Blocks(
            Paragraph(Text("This supplier is part of the natively compiled full ordinary HSW consumer. Apache source selection is from immutable TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, ported at unchanged repository pins. The audit remains unfinished at issue 24542.")),
            Paragraph(Text("spechtModuleComplex(mu) denotes exactly the preserved complex scalar extension of the literal YoungDiagram.ofPartition polytabloid span. Its trace is LinearMap.trace over Complex of its existing action rho. permutationModuleComplex(nu) is the actual complex representation on cosets of youngSubgroup nu. Multiplicity(mu,nu) means Module.finrank Complex of the category Hom from the former representation to the latter. No ordinary character is defined by a polynomial coefficient.")),
            Paragraph(Text("The ordinary-trace certification is consumed to show equality at inverse permutations using their full partitions. The existing D5 FiniteCharacterAlgebra characterPairing_ofFDRep_eq_finrank supplies the character pairing. Combining that pairing with the fixed-tabloid expansion yields the displayed arbitrary-degree polynomial comparison. Its right side contains actual Hom dimensions; identifying these dimensions with Kostka numbers is still missing. Consequently it is not claimed to be the same-shape Schur polynomial.")),
            Paragraph(Text("The second comparison transports the exact existing HSW.frobChar through this fixed-tabloid monomial expansion. fixedTabloids has the meaning above. exponent(mu) is Finsupp.equivFunOnFinite.symm of i mapsto mu(i)+(2-i), with natural subtraction; vandermonde is the existing (X0-X1)(X0-X2)(X1-X2). The list multiset equality keeps every repeated cycle and every one-cycle. This is a fixed-tabloid formula for the existing coefficient, not its ordinary-character identification.")),
            Paragraph(Text("The Young dominance and actual mixed-pairing suppliers feed SpechtThreeRowCauchy, whose finite Cauchy calculation establishes the same-literal-shape trace formula and both evaluated ordinary weighted identities in every degree. The original all-n target, odd rectangles, reciprocal centralizer factors, per-occurrence Ev duplicates and parity-dependent binomial value are unchanged. Issue 21960 remains the full preregistration; issue 22528 concerns only the coefficient audit.")),
            Describe.Lean(DescribeId.Create("sum-specht-trace-smul-psum-part-eq-multiplicities"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtFrobeniusPairing.sum_spechtTrace_smul_psumPart_eq_multiplicities"),
                H("Power sums paired with actual ordinary Specht traces"), StatementSource.FromAuthor(TraceExpansion()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("Necessary source comparison in the full HSW construction. The displayed abbreviations are defined by the narrative above. There is no independent firstfreeze or standalone admission claim; the remaining public-declaration audit is tracked in issue 24542."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hsw-frob-char-eq-fixed-tabloid-coefficients"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtFrobeniusPairing.hsw_frobChar_eq_fixedTabloid_coefficients"),
                H("The exact HSW coefficient through fixed tabloids"), StatementSource.FromAuthor(HswExpansion()),
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
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Times(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Parenthesized(b));
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Inst(string name, Formula x) => Seq(OpenBracket, Call(name, x), CloseBracket, Comma, Sp);
    private static Formula Nat() => Call("Nat");
    private static Formula Complex() => Call("Complex");
    private static Formula Part(Formula n) => Call("Partition", n);
    private static Formula Perm(Formula n) => Call("Perm", Call("Fin", n));
    private static Formula Count(Formula n, Formula nu, Formula pi) => Call("fixedTabloids", n, nu, pi);
    private static Formula Trace(Formula mu, Formula pi) => Call("trace", Complex(), Call("rho", Call("spechtModuleComplex", mu), pi));

    private static Formula TraceExpansion()
    {
        Formula n = Id("n"), sigma = Id("sigma"), mu = Id("mu"), pi = Id("pi"), nu = Id("nu");
        Formula lhs = SumOver("pi", Perm(n), Smul(Trace(mu, pi), Call("psumPart", sigma, Complex(), Call("partition", pi))));
        Formula rhs = Smul(Call("natCast", Call("factorial", n), Complex()), SumOver("nu", Part(n),
            Smul(Call("natCast", Call("Multiplicity", mu, nu), Complex()), Call("msymm", sigma, Complex(), nu))));
        return Disp(All("sigma", Seq(Call("Type"), Star), Seq(Inst("Fintype", sigma),
            All("n", Nat(), All("mu", Part(n), Eq(lhs, rhs))))));
    }
    private static Formula HswExpansion()
    {
        Formula n = Id("n"), mu = Id("mu"), rho = Id("rho"), pi = Id("pi"), tau = Id("tau"), nu = Id("nu");
        Formula body = Eq(Call("HSWfrobChar", mu, tau), SumOver("nu", Part(n), Times(
            Call("natCast", Count(n, nu, pi), Call("Int")), Call("coeff",
                Times(Call("vandermonde"), Call("msymm", Call("Fin", D(3)), Call("Int"), nu)), Call("exponent", mu)))));
        Formula premise = Eq(Call("ConjClassesMk", pi), Call("partitionEquivConjClasses", n, rho));
        Formula listParts = Eq(Call("toMultiset", tau), Call("parts", rho));
        return Disp(All("n", Nat(), All("mu", Seq(Call("Fin", D(3)), To, Nat()), All("rho", Part(n),
            All("pi", Perm(n), Imp(premise, All("tau", Call("List", Nat()), Imp(listParts, body))))))));
    }

}
