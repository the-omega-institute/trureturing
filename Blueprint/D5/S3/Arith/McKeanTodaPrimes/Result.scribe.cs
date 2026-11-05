using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.McKeanTodaPrimes;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Arith/McKeanTodaPrimes/Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/mckean2025todaprimes");
    private const string DefinitionQuote = "Definition 1.1. Let n be an integer. A Toda prime of n is an odd prime p such that p − 1 | 4n and gcd(p, 4n/(p−1)) = 1. Denote the set of Toda primes of n by T (n) (see Table 1), and let t(n) := |T (n)| (see Figure 1).";
    private const string NotationQuote = "Notation 5.5. Given an even integer 2m, let P (2m) denote the set of primes such that p − 1 | 2m, so that D₂ₘ = ∏ₚ∈P(2m) p. Let F (d) = min{2m > 0 : D₂ₘ = d} [PW23].";
    private const string ConjectureQuote = "Conjecture 5.6. Let d be a Bernoulli denominator. (i) If F (d) = 4a for some integer a, then T (am) = T (a) whenever D₄ₐₘ = D₄ₐ. (ii) If D₄ₐₘ ≠ D₄ₐ = d, then t(am) ≥ t(a).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both denominator-based assertions about Toda primes fail.",
        H("Counterexamples to McKean's Conjecture 5.6"), Blocks(
            Node("todaPrimes", "Toda primes", All("n", N, Eq(T(n),
                Filter("p", And(Prime(p), And(Odd(p), And(Dvd(Sub(p, D(1)), Four(n)),
                    Call("Nat.Coprime", p, Div(Four(n), Sub(p, D(1))))))), Range(Add(Four(n), D(2)))))),
                "§1, printed p. 1: “" + DefinitionQuote + "” For positive n, divisibility and primality imply p−1≤4n, hence p<4n+2. The range therefore omits no Toda prime. At n=0 the quotient is zero, and a prime is not coprime to zero, so the set is empty. The natural-number domain suffices to contradict the positive-integer assertion.", true, true),
            Node("t", "Number of Toda primes", All("n", N, Eq(Call("t", n), Call("Finset.card", T(n)))),
                "The cardinality is exactly t(n) in Definition 1.1, §1, printed p. 1.", true, true),
            Node("bernDen", "Reduced Bernoulli denominator", All("k", N,
                Eq(B(k), Call("Rat.den", Call("bernoulli", k)))),
                "Dk is the reduced positive denominator of Bk. Mathlib uses B1=−1/2; all Bernoulli indices in the counterexamples are positive and even.", true, true),
            Node("denominatorPrimes", "Prime predecessors dividing an index", All("k", N,
                Eq(P(k), Filter("p", And(Prime(p), Dvd(Sub(p, D(1)), k)), Range(Add(k, D(2)))))),
                "§5.1, printed p. 8: “" + NotationQuote + "” For k>0, any prime with p−1 dividing k satisfies p<k+2. The finite range is exhaustive.", true, true),
            Node("clauseI", "The denominator-invariance assertion", Eq(V("clauseI"), ClauseOne()),
                "Conjecture 5.6(i), §5.1, printed p. 8: “If F (d) = 4a for some integer a, then T (am) = T (a) whenever D₄ₐₘ = D₄ₐ.” The hypothesis F(bernDen(4a))=4a is encoded equivalently by excluding every smaller positive even index with that denominator. The equality bernDen(4a)=d is automatic for d=bernDen(4a). No choice of a first index is needed.", true, true),
            Node("clauseII", "The denominator-change assertion", Eq(V("clauseII"), ClauseTwo()),
                "Conjecture 5.6(ii), §5.1, printed p. 8: “If D₄ₐₘ ≠ D₄ₐ = d, then t(am) ≥ t(a).” Both multipliers are positive natural numbers.", true, true),
            Node("claim", "The full two-clause conjecture", Eq(V("claim"), And(V("clauseI"), V("clauseII"))),
                "§5.1, printed p. 8: “" + ConjectureQuote + "” The assertion is the conjunction of both clauses with positive a and m. The two clauses are separately refuted below.", true, true),
            Node("memDenominatorPrimes", "The range is exhaustive", All("k", N, All("p", N,
                Imp(Pos(k), Iff(Mem(p, P(k)), And(Prime(p), Dvd(Sub(p, D(1)), k)))))),
                "A positive divisor of k is at most k. This gives the stated membership condition without a range restriction."),
            Node("denominatorFormula", "The exact denominator product", All("k", N,
                Imp(Pos(k), Eq(B(Mul(D(2), k)), ProductPrimes(Mul(D(2), k))))),
                "Bernoulli.vonStaudt_clausen expresses B(2k) as an integer minus the prime reciprocal sum. Finset.Rat.den_sum_dvd_prod_den bounds its denominator by the prime product. Each prime in the product divides the denominator by Bernoulli.dvd_den_bernoulli. Nat.coprime_primes and Finset.prod_dvd_of_isRelPrime give divisibility by their product. Antisymmetry gives equality. This is the denominator identity in Notation 5.5, §5.1, printed p. 8.", false, true),
            Node("todaReduction", "Coprimality removes the prime factors of n", All("n", N, Imp(Pos(n),
                Eq(T(n), Filter("p", And(Odd(p), Not(Dvd(p, n))), P(Four(n)))))),
                "Nat.not_dvd_of_pos_of_lt excludes p dividing p−1. Nat.prime_eq_prime_of_dvd_pow reduces a prime divisor of 4 to 2, which oddness excludes. Nat.mul_div_cancel' gives (p−1)(4n/(p−1))=4n; Nat.Prime.dvd_mul and Nat.Prime.coprime_iff_not_dvd then make coprimality with the quotient equivalent to p not dividing n."),
            Node("compositeByMod", "A proper divisor proves compositeness", All("q", N, All("c", N,
                Imp(Lt(D(1), V("c")), Imp(Lt(V("c"), q), Imp(Eq(Mod(q, V("c")), D(0)), Not(Prime(q))))))),
                "Nat.not_prime_of_dvd_of_lt excludes a number with a divisor strictly between one and itself. Nat.dvd_of_mod_eq_zero supplies the divisor from the zero residue. This excludes the unwanted divisor successors."),
            Node("familyCandidates", "Only four divisor successors can be prime", All("a", N, All("q", N,
                FamilyAssumptions(Imp(Prime(q), Imp(Dvd(Sub(q, D(1)), LargeIndex()), CandidateList()))))),
                "exists_dvd_and_dvd_of_dvd_mul decomposes a divisor of 4a(2a+1) into divisors of 4, a and 2a+1. Nat.dvd_prime_pow classifies the divisors of 4, giving twelve candidates. The unwanted successors are even or divisible by 3 or 5. The residue a≡23 modulo 30 gives a≡1 modulo 2, a≡2 modulo 3 and a≡3 modulo 5."),
            Node("familyPrimeSets", "Both denominator prime sets coincide", All("a", N, FamilyAssumptions(
                And(Eq(P(Four(a)), FourPrimes()), Eq(P(LargeIndex()), FourPrimes())))),
                "The four possible primes 2,3,5,2a+1 all occur. Every divisor successor for 4a is also one for 4a(2a+1)."),
            Node("primeDenIff", "Prime divisibility of an even-index denominator", All("k", N, All("p", N,
                Imp(Pos(k), Imp(Call("Even", k), Imp(Prime(p), Iff(Dvd(p, B(k)), Dvd(Sub(p, D(1)), k))))))),
                "Apply the product formula and prime divisibility of a finite product. A prime dividing another prime is equal to it."),
            Node("familyMinimum", "The first even index is 4a", All("a", N, FamilyAssumptions(
                All("k", N, Imp(Pos(k), Imp(Call("Even", k), Imp(Eq(B(k), ThirtyP()), Le(Four(a), k))))))),
                "primeDenIff applied to 5 and 2a+1 forces 4 dividing k and 2a dividing k. Writing k=2ar, Nat.mul_dvd_mul_iff_left cancels a factor of 2 from 4 dividing k. The odd residue of a then forces r to be even. Nat.pos_of_mul_pos_left gives r>0, and Nat.le_of_dvd gives r≥2, hence k≥4a."),
            Node("family", "The prime family contradicting invariance", All("a", N, FamilyAssumptions(FamilyConclusion())),
                "For every prime a≡23 modulo 30 whose successor 2a+1 is prime, both denominators equal 30(2a+1), their first positive even index is 4a, and multiplication by 2a+1 removes exactly that Toda prime. The assumptions describe a family; infinitude of its members is not asserted."),
            Node("witnessII", "The strict decrease at 11 times 5", And(Eq(B(D(4,4)), D(6,9,0)),
                And(Eq(B(D(2,2,0)), D(7,5,9,0)), And(Eq(T(D(1,1)), Set(D(3), D(5), D(2,3))),
                    Eq(T(D(5,5)), Set(D(3), D(2,3)))))),
                "The product formula gives the denominators 690 and 7590. Direct finite evaluation gives the Toda sets {3,5,23} and {3,23}; the cardinality decreases from three to two. No Bernoulli number at index 220 is directly evaluated."),
            Node("refuteI", "Clause (i) is false", Not(V("clauseI")),
                "The family member a=23, m=47 has first even denominator index 92, unchanged denominator 1410 and unequal Toda sets."),
            Node("refuteII", "Clause (ii) is false", Not(V("clauseII")),
                "At a=11, m=5, the denominator changes from 690 to 7590 while the cardinality decreases from three to two."),
            Node("refutedClauses", "Both clauses are false", And(Not(V("clauseI")), Not(V("clauseII"))),
                "The first counterexample preserves the denominator and violates invariance. The second changes the denominator and violates monotonicity."),
            Node("result", "Conjecture 5.6 is refuted", Not(V("claim")),
                "Both component assertions are false, so their conjunction is false. Question 1.2 and Conjecture 1.3 about existence of Toda primes are not settled.", false, false,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mckean-2025-toda-primes-conjecture"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool definition = false, bool literature = false, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("toda-" + name.ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")), Sp);
    private static Formula n => V("n");
    private static Formula k => V("k");
    private static Formula a => V("a");
    private static Formula m => V("m");
    private static Formula p => V("p");
    private static Formula q => V("q");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var words = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (words.Count > 0) words.Add(Dot);
            words.Add(V(word));
        }
        return new Formula.Apply(Seq(Operatorname, Grp([.. words]), Sp), [.. args]);
    }
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(V(name), Colon, Sp, N)), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Dvd(Formula x, Formula y) => Seq(Parenthesized(x), Sp, Mid, Sp, Parenthesized(y));
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Or, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Not(Formula x) => new Formula.Not(Parenthesized(x));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Parenthesized(x), FormulaBinaryOperator.Multiply, Parenthesized(y));
    private static Formula Div(Formula x, Formula y) => Call("Nat.div", x, y);
    private static Formula Mod(Formula x, Formula y) => Call("Nat.mod", x, y);
    private static Formula Pos(Formula x) => Lt(D(0), x);
    private static Formula Prime(Formula x) => Call("Nat.Prime", x);
    private static Formula Odd(Formula x) => Call("Odd", x);
    private static Formula Four(Formula x) => Mul(D(4), x);
    private static Formula B(Formula x) => Call("bernDen", x);
    private static Formula P(Formula x) => Call("denominatorPrimes", x);
    private static Formula T(Formula x) => Call("todaPrimes", x);
    private static Formula Range(Formula x) => Call("Finset.range", x);
    private static Formula Filter(string name, Formula predicate, Formula set) => Call("Finset.filter", Lam(name, predicate), set);
    private static Formula Set(params Formula[] elements)
    {
        var list = new List<Formula>();
        foreach (var element in elements)
        {
            if (list.Count > 0) list.Add(Comma);
            list.Add(element);
        }
        return Seq(OpenBrace, Seq([.. list]), CloseBrace);
    }
    private static Formula ProductPrimes(Formula index) => Seq(new Formula.Subscript(Prod, Seq(p, Sp, InMacro, Sp, P(index))), Sp, p);
    private static Formula FirstIndex() => All("k", N, Imp(Pos(k), Imp(Call("Even", k), Imp(Lt(k, Four(a)), Not(Eq(B(k), B(Four(a))))))));
    private static Formula ClauseOne() => All("a", N, All("m", N, Imp(Pos(a), Imp(Pos(m), Imp(FirstIndex(),
        Imp(Eq(B(Mul(Four(a), m)), B(Four(a))), Eq(T(Mul(a, m)), T(a))))))));
    private static Formula ClauseTwo() => All("a", N, All("m", N, Imp(Pos(a), Imp(Pos(m),
        Imp(Not(Eq(B(Mul(Four(a), m)), B(Four(a)))), Le(Call("t", a), Call("t", Mul(a, m))))))));
    private static Formula Successor() => Add(Mul(D(2), a), D(1));
    private static Formula LargeIndex() => Mul(Four(a), Successor());
    private static Formula ThirtyP() => Mul(D(3,0), Successor());
    private static Formula FamilyAssumptions(Formula body) => Imp(Prime(a), Imp(Eq(Mod(a, D(3,0)), D(2,3)), Imp(Prime(Successor()), body)));
    private static Formula FourPrimes() => Set(D(2), D(3), D(5), Successor());
    private static Formula CandidateList() => Or(Eq(q, D(2)), Or(Eq(q, D(3)), Or(Eq(q, D(5)), Eq(q, Successor()))));
    private static Formula FamilyConclusion() => And(Eq(B(Four(a)), ThirtyP()), And(Eq(B(LargeIndex()), ThirtyP()),
        And(All("k", N, Imp(Pos(k), Imp(Call("Even", k), Imp(Lt(k, Four(a)), Not(Eq(B(k), ThirtyP())))))),
        And(Eq(T(a), Set(D(3), D(5), Successor())), Eq(T(Mul(a, Successor())), Set(D(3), D(5)))))));
}
