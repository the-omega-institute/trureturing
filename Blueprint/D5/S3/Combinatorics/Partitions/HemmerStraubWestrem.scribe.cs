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
                "Both sides equal 2 to the number of parts times the difference between the coefficients of degrees n and n+1 in the product of X^(2a)+X^a+1 over the parts a. The alternating expansion uses p_a²−p_(2a) in three variables; the other expansion uses p_a²+p_(2a) at (X,1,0). The symmetric homogeneous coefficient detector identifies the first sum with that same difference. The argument applies to any ordered list of positive parts with positive sum, so no single-part-size or sorting hypothesis enters the coefficient argument. The weighted closed-form application of this identity is derived below. The identities for N ≥ 2 and explicit bijective proofs remain open here.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source()),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hemmer-straub-westrem-2025-ev-character-identity"), ResolutionKind.Proved)),
            WeightedApplication()),
        []));

    private static DocumentBlock WeightedApplication() => new DocumentBlock.Section(
        H("The weighted application"), Blocks(
            Paragraph(Text("For every integer n ≥ 1, the two weighted character expressions in Hemmer–Straub–Westrem, arXiv:2509.02796v1, Conjecture 6.1, equation (6.1), are equal to binom(n/2 + 2, 2) when n is even and to zero when n is odd. The journal statement is Conjecture 17, DOI 10.37236/14401. The derivation below uses the pointwise result above and the same Frobenius convention. Its ordinary-character reading uses the classical formula in Lemma 3.1 of the primary manuscript (https://arxiv.org/html/2509.02796v1#S3.Thmtheorem1); the full target is at https://arxiv.org/html/2509.02796v1#S6.E1 and the journal article at https://doi.org/10.37236/14401.")),
            Paragraph(Text("Write m_k(λ) for the multiplicity of the positive part k in λ ⊢ n, r = ℓ(λ), and z_λ = ∏_{k=1}^n k^{m_k(λ)} m_k(λ)!. This is the existing DeformedJucysMurphyC2.zPartition: its partitionExponent records m_k at index k−1. The empty partition has z_∅ = 1. Every occurrence of every part is retained, with no restriction on repeated or mixed part sizes.")),
            Paragraph(Text("Let S_λ = ∑_{τ∈Ev(λ)} ∑_{μ∈R₃(2n)} (−1)^{ℓ(τ)} χ^μ_τ and B_λ = ∑_{τ∈Ev(λ)} χ^{(n,n)}_τ. Here R₃ consists of weakly decreasing even triples of sum 2n, padded by zeros; the rectangle is (n,n,0). Ev is the list of all independent binary replacements of each occurrence a by either (2a) or (a,a). Coincident cycle types are counted with their multiplicity, so there are 2^r choices. Define L_n = ∑_{λ⊢n} S_λ/z_λ and R_n = ∑_{λ⊢n} B_λ/z_λ, taking the integer character sums in ℚ. The existing pointwise result gives S_λ = B_λ for every λ and hence L_n = R_n. It remains to evaluate their common average.")),
            Paragraph(Text("First take arbitrary inputs a_k in a commutative ℚ-algebra and define A_n(a) = ∑_{λ⊢n} (∏_{k=1}^n a_k^{m_k(λ)})/z_λ, with A₀(a) = 1. If λ contains k and ν is obtained by deleting one k, then z_λ = k m_k(λ) z_ν. Thus k m_k(λ) (∏ a_j^{m_j(λ)})/z_λ = a_k (∏ a_j^{m_j(ν)})/z_ν. Deleting a k is a bijection from partitions of n containing k to partitions of n−k; the multiplicity is already in the factor k m_k(λ), so it is not counted a second time.")),
            Paragraph(Text("Summing this equality over λ and then over 1 ≤ k ≤ n, and using ∑_k k m_k(λ) = n, gives n A_n(a) = ∑_{k=1}^n a_k A_{n−k}(a). The centralizer step is supplied by DeformedJucysMurphyC2.zExponent_add_single with i = k−1 and d = partitionExponent ν; positivity follows from zExponent_pos. Mathlib's Nat.Partition.partitionWithPartEquiv supplies the deletion bijection. For A(t) = ∑_{n≥0} A_n(a)t^n, the recurrence says A′(t) = (∑_{k≥1} a_k t^{k−1})A(t), A(0) = 1. In a ℚ-algebra this determines every coefficient uniquely, since each positive integer is invertible.")),
            Paragraph(Text("Now work in ℚ[z,z⁻¹][[t]] and set a_k = 2(z^k + 1 + z^(−k)). The product F(t,z) = (1−t)^(−2)(1−tz)^(−2)(1−t/z)^(−2) has constant coefficient 1 and logarithmic derivative F′/F = 2/(1−t) + 2z/(1−tz) + 2z⁻¹/(1−t/z) = ∑_{k≥1} a_k t^{k−1}. Consequently A(t) = F(t,z). This is an identity of formal power series: each coefficient of t has finite Laurent support, so the products, derivatives and coefficient extractions require no analytic convergence assumption. The existing private LatticeHalfFockChargedCoefficients.solution_unique supplies the required formal differential-equation uniqueness; HasUniqueDiv.of_module_rat provides its additive torsion-free hypothesis.")),
            Paragraph(Text("To connect this series to the character sum, put P_λ(X) = ∏_{a∈λ}(X^{2a}+X^a+1), where the product ranges over all part occurrences. The existing private HemmerStraubWestrem.ev_right and right_coefficient, with triProd, give B_λ = 2^r([X^n]P_λ − [X^{n+1}]P_λ) for every n ≥ 1 and λ ⊢ n. No new character identity is needed. After substituting X = z and multiplying by z⁻ⁿ, the partwise equality z^(−a)(z^{2a}+z^a+1) = z^a+1+z^(−a) gives Q_λ(z) := 2^r z⁻ⁿP_λ(z) = ∏_{k=1}^n a_k^{m_k(λ)}.")),
            Paragraph(Text("With CT denoting the coefficient of z⁰, the adjacent coefficients are [z⁰]Q_λ = 2^r[X^n]P_λ and [z¹]Q_λ = 2^r[X^{n+1}]P_λ. Therefore B_λ = CT((1−z⁻¹)Q_λ). Each factor z^a+1+z^(−a) is invariant under z ↦ z⁻¹; hence Q_λ and F are symmetric Laurent series. In particular [z¹]Q_λ = [z⁻¹]Q_λ and CT((1−z⁻¹)Q_λ) = CT((1−z)Q_λ). These are the same adjacent-coefficient convention, related by symmetry.")),
            Paragraph(Text("Linearity now gives R_n = CT((1−z⁻¹)A_n(a)) for n ≥ 1. To evaluate all these coefficients together, define C(t) = CT((1−z⁻¹)F(t,z)); its constant term is 1 from the empty-partition series. The positive-degree coefficients are exactly R_n. It remains to compute this constant term explicitly.")),
            Paragraph(Text("Write G(t,z) = (1−tz)^(−2)(1−t/z)^(−2). Since (1−u)^(−2) = ∑_{j≥0}(j+1)u^j, we have G(t,z) = ∑_{i,j≥0}(i+1)(j+1)t^{i+j}z^{i−j}. The condition i−j = 0 gives CT G = ∑_{j≥0}(j+1)²t^{2j}; the condition i−j = 1 gives CT(z⁻¹G) = ∑_{j≥0}(j+1)(j+2)t^{2j+1}. Thus C(t) = (1−t)^(−2)(∑_{j≥0}(j+1)²t^{2j} − t∑_{j≥0}(j+1)(j+2)t^{2j}).")),
            Paragraph(Text("For a formal variable q, ∑_{j≥0}(j+1)(j+2)q^j = 2/(1−q)³, because (j+1)(j+2) = 2 binom(j+2,2). Also ∑_{j≥0}(j+1)²q^j = 2/(1−q)³ − 1/(1−q)² = (1+q)/(1−q)³, because (j+1)² = 2 binom(j+2,2) − (j+1). Substitution q = t² makes the difference in parentheses equal to (1+t²−2t)/(1−t²)³ = (1−t)²/(1−t²)³. The factor (1−t)^(−2) therefore cancels exactly, giving C(t) = (1−t²)^(−3). All cancelled factors have constant coefficient 1 and are units in the formal power series ring.")),
            Paragraph(Text("Finally, (1−t²)^(−3) = ∑_{m≥0} binom(m+2,2)t^{2m}. It follows that L_n = R_n = binom(n/2+2,2) for even n and L_n = R_n = 0 for odd n, for every n ≥ 1. On the even branch n/2 is the integer m with n = 2m; the corresponding Lean expression is ((n / 2 + 2).choose 2 : ℕ) cast to ℚ. Both equalities of the source statement follow, with every partition and every independent Ev choice included.")),
            Paragraph(Text("The complete published weighted proof source is https://github.com/the-omega-institute/trureturing/blob/69f68474a0566d6f465a14259b74f28b58e293f3/D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.lean. This application reuses the owning pointwise result, its private rectangular coefficient suppliers, the C2 centralizer declarations and formal power-series identities. The application introduces no new frozen weighted theorem. The literature identification with ordinary irreducible characters is Lemma 3.1; equivalence with an internal partition-indexed Specht/trace construction remains unproved. The N ≥ 2 identities and explicit bijective proofs remain separate mathematical questions."))));

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
