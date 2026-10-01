using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class OeisA400168PrimorialGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/OeisA400168PrimorialGap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/karttunen2026a400168");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A400168 has a term above one: at n = 2^49 the term is two.",
        H("A positive answer to the A400168 question"),
        Blocks(
            Paragraph(Text(
                "Antti Karttunen, OEIS A400168, revision 8: \"Question: Are there terms "
                    + "greater than 1?\" The entry defines a(n) = A235224(A003415(n)) "
                    + "- A400164(n), with offset one. It asks an existence question.")),
            Node("indexed-primorial", "Indexed primorials", PrimorialFormula(),
                "P(0) = 1. For k >= 1, P(k) is the product of the first k primes, "
                    + "as in A002110. nthPrime(k) is the zero-based enumeration Nat.nth "
                    + "Nat.Prime k. primorial(q) multiplies the primes at most q; hence "
                    + "primorial(nthPrime(k)) contains exactly the first k + 1 primes. "
                    + "Each new prime is at least two, so P is strictly increasing. "
                    + "The index of P counts primes and is not a prime-value bound.",
                "P", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("primorial-length", "Primorial length", LengthFormula(),
                "L(m) is the least natural k with m < P(k). Such k exists for every m: "
                    + "P(m + 1) is at least nthPrime(m), which is at least m + 2. "
                    + "The least threshold definition has no finite search cap. P(0) = 1 "
                    + "gives L(0) = 0. For m > 0, L(m) = j + 1 precisely when "
                    + "P(j) <= m < P(j + 1). Strict increase then makes L(m) the largest "
                    + "k >= 1 with P(k - 1) <= m, exactly the NAME of A235224. "
                    + "In particular L(1) = 1. The displayed characterization includes zero "
                    + "and all positive arguments; minimality also implies monotonicity in m.",
                "L", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("arithmetic-derivative", "Arithmetic derivative", DerivativeFormula(),
                "factorization(n) records the finite prime multiplicities v_p(n), and sum "
                    + "denotes Finsupp.sum over its support. NatDiv is natural integer division. "
                    + "Thus D(n) sums v_p(n) times n/p over exactly the primes dividing n. "
                    + "This is the factorization formula for A003415. For each summand p divides "
                    + "n, so division is exact. The empty factorizations give D(0) = D(1) = 0. "
                    + "Prime inputs give one, and addition of prime multiplicities for a "
                    + "product yields D(mn) = D(m)n + mD(n), including zero factors.",
                "D", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("prime-power-maximum", "Maximum over prime-power divisors", MaximumFormula(),
                "divisors(n) is the finset of positive divisors, and filter retains precisely "
                    + "IsPrimePow divisors. On naturals IsPrimePow means p^e with p prime and "
                    + "e >= 1, matching A246655; one is excluded. sup is the maximum of the "
                    + "natural values, with zero for an empty finset. Hence M(1) = 0 and for "
                    + "every n >= 2, M(n) equals the A400164 maximum over all prime-power "
                    + "divisors d = p^e of L(n/d). No exponent or divisor is omitted, including "
                    + "d = n when n is a prime power. The harmless extension M(0) = 0 is outside "
                    + "the question's positive-index domain.",
                "M", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("universal-negative-answer", "The universal negative answer", ClaimFormula(),
                "claim is the universal negative answer, not a conjecture asserted by "
                    + "Karttunen. For natural lengths, a(n) > 1 is equivalent to "
                    + "L(D(n)) > M(n) + 1, whether subtraction in the sequence is read "
                    + "as integer subtraction or natural subtraction. Negating the displayed "
                    + "universal statement is therefore equivalent to existence of a natural "
                    + "n >= 1 with a(n) > 1. This covers the complete original question, "
                    + "with all positive indices and the zero conventions in its component functions.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("positive-answer", "The term at two to the forty-ninth power",
                Disp(new Formula.Not(F.Id("claim"))),
                "At n = 2^49 = 562949953421312, D(n) = 49 times 2^48 "
                    + "= 13792273858822144. Every prime-power divisor is 2^e with "
                    + "1 <= e <= 49, so n/d <= 2^48, with equality at d = 2. "
                    + "P(12) = 7420738134810 <= 2^48 = 281474976710656 "
                    + "< 304250263527210 = P(13), giving M(n) = 13. "
                    + "P(14) = 13082761331670030 <= D(n) "
                    + "< 614889782588491410 = P(15), giving L(D(n)) = 15. "
                    + "Consequently a(n) = 15 - 13 = 2 > 1. The universal negative answer "
                    + "is false and the original existence question is answered yes. "
                    + "No least-index or infinite-family assertion is made.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula PrimorialFormula() => Disp(And(
        Equal(Call("P", D(0)), D(1)),
        All("k", Equal(Call("P", Add(F.Id("k"), D(1))),
            Call("primorial", Call("nthPrime", F.Id("k")))))));

    private static Formula LengthFormula()
    {
        var m = F.Id("m");
        var k = F.Id("k");
        var j = F.Id("j");
        var minimal = And(Less(m, Call("P", k)),
            All("j", Implies(Less(j, k), AtMost(Call("P", j), m))));
        return Disp(All("m", All("k", new Formula.Logic(Equal(Call("L", m), k),
            FormulaLogicOperator.Iff, minimal))));
    }

    private static Formula DerivativeFormula()
    {
        var n = F.Id("n");
        var summand = Lambda("p", Lambda("e",
            Multiply(F.Id("e"), Call("NatDiv", n, F.Id("p")))));
        return Disp(All("n", Equal(Call("D", n),
            Call("sum", Call("factorization", n), summand))));
    }

    private static Formula MaximumFormula()
    {
        var n = F.Id("n");
        var divisors = Call("filter", Call("divisors", n), F.Id("IsPrimePow"));
        var value = Lambda("d", Call("L", Call("NatDiv", n, F.Id("d"))));
        return Disp(All("n", Equal(Call("M", n), Call("sup", divisors, value))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var bound = AtMost(Call("L", Call("D", n)), Add(Call("M", n), D(1)));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All("n", Implies(AtMost(D(1), n), bound))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Naturals(), body);
    private static Formula Lambda(string name, Formula body) => Seq(F.Id(name), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Multiply(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
