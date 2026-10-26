using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class DeCastroIntegersConjecture1Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/DeCastroIntegersConjecture1.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/decastro2022binomialorders");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power denominator saturation proves de Castro’s admissible-fraction formula.",
        H("DeCastroIntegersConjecture1"),
        Blocks(
            Node("frac", "The binomial fraction", FractionBody(),
                "Definition 2 (p. 7): “Let S^min_{p,n} and S^max_{p,n} denote sets of irreducible fractions given by S^min_{p,n} = {(1/n) binomial(n, p_i^j) | i ∈ N*, j ∈ N, gcd(p_i^j, p) = 1, p_i^j ≤ n}, S^max_{p,n} = {(1/n) binomial(n, k) | 0 < k ≤ n, gcd(k, p) = 1}.” The rational number (1/n) binomial(n,k) is the fraction used in both sets.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Smin", "The lower set of fractions", SetMinimum(),
                "Definition 2 (p. 7): “Let S^min_{p,n} and S^max_{p,n} denote sets of irreducible fractions given by S^min_{p,n} = {(1/n) binomial(n, p_i^j) | i ∈ N*, j ∈ N, gcd(p_i^j, p) = 1, p_i^j ≤ n}, S^max_{p,n} = {(1/n) binomial(n, k) | 0 < k ≤ n, gcd(k, p) = 1}.” The i-th prime is Nat.nth Nat.Prime (i-1), with i ≥ 1 and j ≥ 0. Subtraction of indices is in the natural numbers.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Smax", "The upper set of fractions", SetMaximum(),
                "Definition 2 (p. 7): “Let S^min_{p,n} and S^max_{p,n} denote sets of irreducible fractions given by S^min_{p,n} = {(1/n) binomial(n, p_i^j) | i ∈ N*, j ∈ N, gcd(p_i^j, p) = 1, p_i^j ≤ n}, S^max_{p,n} = {(1/n) binomial(n, k) | 0 < k ≤ n, gcd(k, p) = 1}.” Fractions are elements of the rationals in lowest terms.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", Eqn(Seq(Operatorname, Grp(X("claim"))), Parenthesized(ClaimBody())),
                "Conjecture 1 (p. 7): “Given any admissible set S_{p,n}, the p-adic order of a positive integer n can be expressed as v_p(n) = log_p(n / L_{p,n}), where L_{p,n} represents the least common denominator of the elements of S_{p,n}.” The order is padicValNat, the logarithm is Real.logb, and the least common denominator is Finset.lcm applied to Rat.den. Natural values are explicitly cast to the reals.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("den_dvd_k", "The denominator divides the lower binomial index", DenominatorBound(true),
                "For positive n and k, the identity binomial(n,k)/n = binomial(n-1,k-1)/k bounds the reduced denominator by k.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("den_dvd_gcd", "The common divisor bound", GcdBound(),
                "For positive n and k, the reduced denominator divides gcd(n,k). This bound also applies to composite bases.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("den_prime_pow", "Saturation at a prime-power divisor", Saturation(),
                "If a prime power p^j divides positive n, the binomial fraction at index p^j has denominator exactly p^j. The exponent j=0 is included. Lucas congruences show that the shifted binomial numerator is prime to p.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("logarithm_iff", "The logarithmic equation as a natural identity", Logarithm(),
                "For q>1 and positive n and l, the real logarithmic equation is equivalent to q^e*l=n in the naturals.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("result", "De Castro Conjecture 1", ClaimBody(),
                "The prime-power fractions in Smin provide every prime-power divisor of n away from p. The gcd bound excludes p and any larger denominator, so the lcm is n.divMaxPow p. The factorization of n then gives the logarithmic equation.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("decastrointegersconjecture1-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(X(name))), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula R() => Seq(Mathbb, Grp(X("R")));
    private static Formula Rat() => Seq(Mathbb, Grp(X("Q")));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Dvd(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Sp, Colon, Sp, type));
    private static Formula Prime(Formula p) => App(Q("Nat", "Prime"), p);
    private static Formula FinsetRat() => Call("Finset", Rat());
    private static Formula Den(Formula a) => App(Q("Rat", "den"), a);
    private static Formula Lcm(Formula s) => App(Q("Finset", "lcm"), s, Q("Rat", "den"));
    private static Formula Nth(Formula i) => App(Q("Nat", "nth"), Q("Nat", "Prime"), Sub(i, D(1)));
    private static Formula Frac(Formula n, Formula k) => Mul(new Formula.Fraction(D(1), Cast(n, Rat())), Cast(App(Q("Nat", "choose"), n, k), Rat()));
    private static Formula Order(Formula p, Formula n) => Cast(Call("padicValNat", p, n), R());
    private static Formula LogRatio(Formula p, Formula n, Formula l) => App(Q("Real", "logb"), Cast(p, R()), new Formula.Fraction(Cast(n, R()), Cast(l, R())));

    private static Formula ClaimBody()
    {
        var p = X("p"); var n = X("n"); var s = X("S");
        return All("p", N(), All("n", N(), Imp(Prime(p), Imp(Leq(D(1), n),
            All("S", FinsetRat(), Imp(Admissibility(p, n, s), Eqn(Order(p, n), LogRatio(p, n, Lcm(s)))))))));
    }
    private static Formula SetMinimum()
    {
        var p = X("p"); var n = X("n"); var x = X("x"); var i = X("i"); var j = X("j");
        var k = Pow(Nth(i), j);
        var body = Ex("i", N(), Ex("j", N(), And(Leq(D(1), i), And(Eqn(App(Q("Nat", "gcd"), k, p), D(1)), And(Leq(k, n), Eqn(x, Frac(n, k)))))));
        return All("p", N(), All("n", N(), Eqn(Call("Smin", p, n), Seq(OpenBrace, Cast(x, Rat()), Sp, Bar, Sp, body, CloseBrace))));
    }
    private static Formula SetMaximum()
    {
        var p = X("p"); var n = X("n"); var x = X("x"); var k = X("k");
        var body = Ex("k", N(), And(Less(D(0), k), And(Leq(k, n), And(Eqn(App(Q("Nat", "gcd"), k, p), D(1)), Eqn(x, Frac(n, k))))));
        return All("p", N(), All("n", N(), Eqn(Call("Smax", p, n), Seq(OpenBrace, Cast(x, Rat()), Sp, Bar, Sp, body, CloseBrace))));
    }
    private static Formula Admissibility(Formula p, Formula n, Formula s)
    {
        var set = Cast(s, Call("Set", Rat()));
        return And(Seq(Call("Smin", p, n), Sp, Subseteq, Sp, set),
            Seq(set, Sp, Subseteq, Sp, Call("Smax", p, n)));
    }
    private static Formula FractionBody() => All("n", N(), All("k", N(), Eqn(Call("frac", X("n"), X("k")), Frac(X("n"), X("k")))));
    private static Formula DenominatorBound(bool index)
    {
        var n = X("n"); var k = X("k"); var body = Dvd(Den(Call("frac", n, k)), index ? k : n);
        return All("n", N(), All("k", N(), index ? Imp(Less(D(0), n), Imp(Less(D(0), k), body)) : body));
    }
    private static Formula GcdBound()
    {
        var n = X("n"); var k = X("k");
        return All("n", N(), All("k", N(), Imp(Less(D(0), n), Imp(Less(D(0), k), Dvd(Den(Call("frac", n, k)), App(Q("Nat", "gcd"), n, k))))));
    }
    private static Formula Saturation()
    {
        var n = X("n"); var p = X("p"); var j = X("j"); var power = Pow(p, j);
        return All("n", N(), All("p", N(), All("j", N(), Imp(Less(D(0), n), Imp(Prime(p), Imp(Dvd(power, n), Eqn(Den(Call("frac", n, power)), power)))))));
    }
    private static Formula Logarithm()
    {
        var q = X("q"); var n = X("n"); var l = X("l"); var e = X("e");
        return All("q", N(), All("n", N(), All("l", N(), All("e", N(), Imp(Less(D(1), q), Imp(Less(D(0), n), Imp(Less(D(0), l),
            new Formula.Logic(Eqn(Cast(e, R()), LogRatio(q, n, l)), FormulaLogicOperator.Iff, Eqn(Mul(Pow(q, e), l), n)))))))));
    }
}
