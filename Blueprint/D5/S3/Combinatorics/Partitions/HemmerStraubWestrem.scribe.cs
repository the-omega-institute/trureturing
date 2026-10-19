using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class HemmerStraubWestremDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.";
    private static LibraryNoteRef Source() => LibraryNoteRef.Create("D5/L/FiniteGroups/hemmerstraubwestrem2025riordan");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The alternating Ev sum over even three-row characters equals the Ev sum of the two-row character for every partition of positive size.",
        H("The Hemmer–Straub–Westrem Ev character identity"),
        Blocks(
            Node("hsw-power-sum-product", "The power-sum product", "powerSumProd", PowerSumFormula(),
                "For a list of cycle lengths, multiply the three-variable power sums, retaining every occurrence of a length. Here psum is Mathlib's sum of the powers of the three variables.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsw-vandermonde", "The three-variable alternant", "vandermonde3", VandermondeFormula(),
                "The Vandermonde factor corresponds to the exponent shift (2,1,0).", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsw-frobenius-character", "The Frobenius coefficient", "frobChar", CharacterFormula(),
                "Lemma 3.1, page 5, states: “Let µ, λ ⊢ n. We have: χ^µ_λ = ⟨p_λ, s_µ⟩.” The displayed coefficient is the three-variable Frobenius expression for this irreducible character, for partitions with at most three parts padded by zeros. Its identification with the representation-theoretic character is a literature input; it is not formalized here. The index subtraction is truncated subtraction in Nat.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsw-ev-types", "The multiset of doubled cycle types", "evTypes", EvFormula(),
                "Page 1 states: “In [Amd23], Amdeberhan defined Ev(λ) to be the set of all partitions of 2n obtained by replacing each λᵢ with either 2λᵢ or two copies of λᵢ, and then reordering the parts to be nonincreasing.” Each occurrence of a part a contributes either (2a) or (a,a). The list retains multiplicity and represents cycle lengths before sorting; frobChar is unchanged by permuting that list. Section 2.1, page 4, gives multiplicities 1,4,6,4,1 for the five cycle types in Ev((1,1,1,1)). The two equations include the empty-list case.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsw-even-three-rows", "Even partitions with at most three parts", "R3", RowsFormula(),
                "Page 3 states: “When N = 1, the set R^c_{2N}(2n) is the single partition (n, n), and the set R_{2N+1}(2n) consists of all partitions of 2n with at most three parts, all even.” antidiagonalTuple enumerates triples with the indicated sum; the filter requires decreasing order and even entries, including zero padding.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsw-claim", "Conjecture 2.3", "claim", Disp(IffFormula(Call("claim"), ClaimBody())),
                "Conjecture 2.3 (N = 1 version), page 3, states: “For any partition λ ⊢ n, we have ∑_{λ̃∈Ev(λ)} ∑_{µ∈R₃(2n)} (−1)^{ℓ(λ̃)} χ^µ_{λ̃} = ∑_{λ̃∈Ev(λ)} χ^{(n,n)}_{λ̃}. (2.4)” The encoding takes n ≥ 1 and lam : Nat.Partition n, lists its positive parts, and preserves multiplicities in both Ev sums. τ.length is the number of parts and ![n,n,0] pads the two-row partition by zero.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source())),
            Node("hsw-result", "The identity for every partition", "result", Disp(ClaimBody()),
                "Both sides equal 2 to the number of parts times the difference between the coefficients of degrees n and n+1 in the product of X^(2a)+X^a+1 over the parts a. The alternating expansion uses p_a²−p_(2a) in three variables; the other expansion uses p_a²+p_(2a) at (X,1,0). The symmetric homogeneous coefficient detector identifies the first sum with that same difference. The argument applies to any ordered list of positive parts with positive sum, so no single-part-size or sorting hypothesis enters the coefficient argument. The identities for N ≥ 2, the closed form of Conjecture 6.1, and explicit bijective proofs remain separate questions.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source()),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hemmer-straub-westrem-2025-ev-character-identity"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(X(name))) : App(Seq(Operatorname, Grp(X(name))), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Fun(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Call("fun"), Parenthesized(Seq(X(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula NatType() => Call("Nat");
    private static Formula IntType() => Call("Int");
    private static Formula FinThree() => Call("Fin", D(3));
    private static Formula ListNat() => Call("List", NatType());
    private static Formula TripleType() => new Formula.TypeArrow(FinThree(), NatType());
    private static Formula Prod(Formula list) => App(Qualified("List", "prod"), list);
    private static Formula SumList(Formula list) => App(Qualified("List", "sum"), list);
    private static Formula Map(Formula fn, Formula list) => App(Qualified("List", "map"), fn, list);
    private static Formula Empty() => Seq(OpenBracket, CloseBracket);
    private static Formula Cons(Formula a, Formula l) => Parenthesized(Seq(a, Colon, Colon, l));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Multiply(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);

    private static Formula PowerSumFormula() => Disp(All("tau", ListNat(), Equal(
        Call("powerSumProd", X("tau")), Prod(Map(
            App(Qualified("MvPolynomial", "psum"), FinThree(), IntType()), X("tau"))))));

    private static Formula VandermondeFormula()
    {
        Formula a = App(Qualified("MvPolynomial", "X"), D(0)), b = App(Qualified("MvPolynomial", "X"), D(1)), c = App(Qualified("MvPolynomial", "X"), D(2));
        return Disp(Equal(Call("vandermonde3"), Multiply(Multiply(
            Parenthesized(Seq(a, Minus, b)), Parenthesized(Seq(a, Minus, c))), Parenthesized(Seq(b, Minus, c)))));
    }

    private static Formula CharacterFormula()
    {
        Formula mu = X("mu"), tau = X("tau"), i = X("i");
        Formula cast = Parenthesized(Seq(i, Colon, Sp, NatType()));
        Formula shift = Fun("i", FinThree(), Seq(App(mu, i), Plus, Parenthesized(Seq(D(2), Minus, cast))));
        Formula equiv = Seq(Qualified("Finsupp", "equivFunOnFinite"), Dot, Call("symm"));
        return Disp(All("mu", TripleType(), All("tau", ListNat(), Equal(
            Call("frobChar", mu, tau), App(Qualified("AddMonoidAlgebra", "coeff"),
                Multiply(Call("vandermonde3"), Call("powerSumProd", tau)), App(equiv, shift))))));
    }

    private static Formula EvFormula()
    {
        Formula a = X("a"), l = X("l"), tau = X("tau"), rest = Call("evTypes", l);
        Formula one = Map(Fun("tau", ListNat(), Cons(Multiply(D(2), a), tau)), rest);
        Formula two = Map(Fun("tau", ListNat(), Cons(a, Cons(a, tau))), rest);
        return Disp(And(Equal(Call("evTypes", Empty()), Seq(OpenBracket, Empty(), CloseBracket)),
            All("a", NatType(), All("l", ListNat(), Equal(Call("evTypes", Cons(a, l)),
                App(Qualified("List", "append"), one, two))))));
    }

    private static Formula RowsFormula()
    {
        Formula mu = X("mu"), m = X("m"), i = X("i");
        Formula predicate = Fun("mu", TripleType(), And(AtMost(App(mu, D(1)), App(mu, D(0))),
            And(AtMost(App(mu, D(2)), App(mu, D(1))), All("i", FinThree(), Call("Even", App(mu, i))))));
        Formula anti = Seq(Qualified("Finset", "Nat"), Dot, Call("antidiagonalTuple"));
        return Disp(All("m", NatType(), Equal(Call("R3", m),
            App(Qualified("Finset", "filter"), predicate, App(anti, D(3), m)))));
    }

    private static Formula ClaimBody()
    {
        Formula n = X("n"), lam = X("lam"), tau = X("tau"), mu = X("mu");
        Formula parts = Seq(lam, Dot, Call("parts"), Dot, Call("toList"));
        Formula ev = Call("evTypes", parts);
        Formula signed = Multiply(Power(Parenthesized(Seq(Minus, D(1), Colon, Sp, IntType())),
            App(Qualified("List", "length"), tau)), Call("frobChar", mu, tau));
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(mu, Sp, InMacro, Sp, Call("R3", Multiply(D(2), n)))), Sp, Parenthesized(signed));
        Formula triple = Seq(Bang, OpenBracket, n, Comma, n, Comma, D(0), CloseBracket);
        Formula lhs = SumList(Map(Fun("tau", ListNat(), sum), ev));
        Formula rhs = SumList(Map(Fun("tau", ListNat(), Call("frobChar", triple, tau)), ev));
        return All("n", NatType(), Imp(AtMost(D(1), n), All("lam", App(Qualified("Nat", "Partition"), n), Equal(lhs, rhs))));
    }
}
