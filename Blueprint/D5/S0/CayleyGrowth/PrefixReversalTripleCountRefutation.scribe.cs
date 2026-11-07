using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.CayleyGrowth;

internal sealed class PrefixReversalTripleCountRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/CayleyGrowth/PrefixReversalTripleCountRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/CayleyGrowth/blanco2026triplecount");

    private const string SourceQuote = "Conjecture 1, page 17: “Let f(n) be the number of pairs (m,k) such that 2 ≤ k < m < n and ⟨rₙ, rₘ, rₖ⟩ = Symₙ. Then f(n) = { (1/13)n² + O(n), n = 0 (mod 4); (1/9)n² + O(n), n = 1 (mod 4); (1/10)n² + O(n), n = 2 (mod 4); (1/7)n² + O(n), n = 3 (mod 4). }”";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A congruence sieve gives a quadratic upper bound strictly below the proposed coefficient at degrees divisible by four.",
        H("Refutation of the prefix-reversal triple count asymptotic"),
        Blocks(
            Node("f", "Number of generating pairs", CountFormula(), true, true,
                SourceQuote + " "
                + "The source positions j in {1,...,n} correspond to i = j - 1 in Fin n. "
                + "The permutation prefixReversal of length L sends i < L to L - 1 - i and fixes the other indices. "
                + "The subgroup tripleSubgroup is the closure of exactly the three reversals. "
                + "The coordinates p.1 and p.2 are m and k. Their strict ordering counts each pair once. "
                + "The two proofs of length at most n are supplied by the Fin bounds."),
            Node("leadingCoefficient", "The four proposed coefficients", CoefficientFormula(), true, true,
                SourceQuote + " These are real quotients. "
                + "The last branch of the match is used for q.val = 3 because q : Fin 4."),
            Node("claim", "Conjecture 1 with all asymptotic quantifiers",
                Equal(V("claim"), Parenthesized(ClaimBody())), true, true,
                SourceQuote + " "
                + "For each residue q, one nonnegative real C and one natural threshold N must work for every subsequent n in that residue. "
                + "The operation n % 4 is the natural remainder, and the absolute value and polynomial are real."),
            Node("result", "The four-clause asymptotic is false",
                new Formula.Not(Parenthesized(ClaimBody())), false, false,
                "For n divisible by four, generation forces m + k ≥ n, opposite parities for m and k, "
                + "and at least one of m and k to have residue two or three modulo four. "
                + "For every integer p with 3 ≤ p ≤ n, the simultaneous congruences m ≡ k ≡ n modulo p "
                + "would preserve the proper nonempty set of positions with i ≡ 0 or i + 1 ≡ n modulo p. "
                + "Apply these exclusions at p = 3, 5, 7, 11, 13, 17, 19. The Chinese remainder theorem leaves "
                + "115579079884800 pairs of residues modulo 19399380. In each residue pair a finite lattice estimate "
                + "bounds four times the squared modulus times the number of pairs by (n + 38798760)². "
                + "Thus f(n) ≤ (1146617856/14933966047)n² + 58198140n for every n ≥ 19399380 divisible by four. "
                + "The difference 1/13 - 1146617856/14933966047 is the positive number 2148763/14933966047. "
                + "Its quadratic contribution exceeds every proposed linear error along sufficiently large multiples of four. "
                + "The other three residue assertions, the exact limiting coefficient, the existence of a limit and a matching lower bound remain open. "
                + "The argument gives necessary conditions for generation and does not assert their sufficiency."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        bool definition, bool literature, string prose) => Describe.Lean(
            DescribeId.Create("prefixreversaltriplecount-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        App(Seq(Operatorname, Grp(V(name))), arguments);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Coordinate(Formula p, byte index) => Seq(p, Dot, D(index));

    private static Formula CountFormula()
    {
        Formula n = V("n"), p = V("p");
        var m = Call("val", Coordinate(p, 1));
        var k = Call("val", Coordinate(p, 2));
        var pairType = Seq(Call("Fin", n), Times, Call("Fin", n));
        var condition = And(Le(D(2), k), And(Less(k, m),
            Equal(App(Qualified("PrefixReversalTripleOddNonGeneration", "tripleSubgroup"), n, m, k),
                Qualified("Top", "top"))));
        var subtype = Seq(OpenBrace, p, Colon, Sp, pairType, Sp, Slash, Slash, Sp, condition, CloseBrace);
        return All("n", NatType(), Equal(Call("f", n), App(Qualified("Nat", "card"), Parenthesized(subtype))));
    }

    private static Formula CoefficientFormula()
    {
        var q = V("q");
        var body = Seq(Operatorname, Grp(V("match")), Sp, Call("val", q), Sp,
            Operatorname, Grp(V("with")), Sp,
            new Formula.Aligned([
                Seq(D(0), Sp, Mapsto, Sp, new Formula.Fraction(D(1), D(1, 3))),
                Seq(D(1), Sp, Mapsto, Sp, new Formula.Fraction(D(1), D(9))),
                Seq(D(2), Sp, Mapsto, Sp, new Formula.Fraction(D(1), D(1, 0))),
                Seq(Operatorname, Grp(V("otherwise")), Sp, Mapsto, Sp, new Formula.Fraction(D(1), D(7)))]));
        return All("q", Call("Fin", D(4)), Equal(Call("leadingCoefficient", q), body));
    }

    private static Formula ClaimBody()
    {
        Formula q = V("q"), c = V("C"), n = V("n"), threshold = V("N");
        var nr = Cast(n, RealType());
        var error = new Formula.Absolute(Sub(Cast(Call("f", n), RealType()),
            Mul(Call("leadingCoefficient", q), new Formula.Power(nr, D(2)))));
        return All("q", Call("Fin", D(4)), Some("C", RealType(),
            And(Le(D(0), c), Some("N", NatType(), All("n", NatType(),
                Implies(Le(threshold, n), Implies(Equal(new Formula.Modulo(n, D(4)), Call("val", q)),
                    Le(error, Mul(c, nr)))))))));
    }
}
