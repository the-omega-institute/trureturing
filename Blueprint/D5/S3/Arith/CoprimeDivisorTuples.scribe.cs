using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class CoprimeDivisorTuplesDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/CoprimeDivisorTuples.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/wiseman2021a062319");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairwise coprime ordered tuples of divisors of a number are counted by a product "
            + "over its primes, and at tuple length equal to the number itself that product "
            + "counts the divisors of the number raised to itself.",
        H("Pairwise Coprime Tuples of Divisors Count the Divisors of a Self Power"),
        Blocks(
            Node("tuples-of-divisors", "Tuples of divisors that are pairwise coprime",
                "coprimeDivisorTuples", TupleSetFormula(),
                "A tuple of the stated length assigns a divisor of the number to each index. "
                    + "It is pairwise coprime when any two coordinates at distinct indices have "
                    + "greatest common divisor one. Nothing forbids the value one, and nothing "
                    + "forbids it from repeating, so the constant tuple of ones always belongs; "
                    + "the order of the coordinates matters, so a pair and its transpose are "
                    + "counted separately. The worked lists printed on the source entry for the "
                    + "lengths one through five fix both readings. The length is carried as a "
                    + "parameter separate from the number, because the count is a product over "
                    + "the primes of the number only once the length is held fixed; tying the "
                    + "length to the number destroys that independence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjectured-identity", "The conjectured identity", "claim",
                ClaimFormula(),
                "The source asserts that for a positive number, the pairwise coprime ordered "
                    + "tuples of divisors whose length equals the number itself are as many as "
                    + "the divisors of the number raised to its own power, and reports the "
                    + "assertion checked as far as thirty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("identity-holds", "The identity holds", "result", ResultFormula(),
                "Both sides are the same product over the primes dividing the number. For the "
                    + "right side, the exponent of a prime in the self power is the number times "
                    + "its exponent in the number, so the divisor count of the self power is the "
                    + "product over the primes of one more than the number times the exponent. "
                    + "For the left side, pairwise coprimality says exactly that each prime "
                    + "dividing the number divides at most one coordinate. A tuple therefore "
                    + "splits into one independent choice per prime: either no coordinate "
                    + "carries the prime, which is one possibility, or a single coordinate "
                    + "carries it to an exponent between one and its exponent in the number, "
                    + "which is the length times that exponent. Summing the two cases gives the "
                    + "same factor at every prime. The argument is carried out by identifying a "
                    + "divisor with its bounded exponent vector, reading coprimality as the "
                    + "absence of a prime with positive exponent on both sides, and identifying "
                    + "a column of the exponent matrix with either the empty choice or a pair "
                    + "consisting of a coordinate and a positive exponent. Holding the length "
                    + "fixed and letting the number vary proves more than was asserted: for "
                    + "every length the count is the corresponding product, and the source "
                    + "assertion is the diagonal where the length equals the number. The number "
                    + "one needs no separate treatment, since its set of primes is empty and the "
                    + "empty product is one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("coprime-divisor-tuples"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Tuples(Formula k, Formula n) =>
        Seq(F.Id("coprimeDivisorTuples"), Open, k, Comma, Sp, n, Close);

    private static Formula Apply(Formula f, Formula x) => Seq(f, Open, x, Close);

    private static Formula GcdOf(Formula a, Formula b) =>
        Seq(Gcd, Sp, Open, a, Comma, Sp, b, Close);

    private static Formula Card(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);

    private static Formula Divisors(Formula x) => Seq(F.Id("divisors"), Open, x, Close);

    private static Formula SelfPower(Formula n) => Seq(n, Caret, Grp(n));

    private static Formula IndexSet(Formula k) => Seq(F.Id("Fin"), Sp, k);

    private static Formula TupleSetFormula()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var f = F.Id("f");
        var i = F.Id("i");
        var j = F.Id("j");
        var divides = Universal("i", IndexSet(k), Divides(Apply(f, i), n));
        var coprime = Universal("i", IndexSet(k),
            Universal("j", IndexSet(k),
                Implies(NotEqual(i, j), Equal(GcdOf(Apply(f, i), Apply(f, j)), D(1)))));
        return Disp(Equal(Tuples(k, n),
            Seq(OpenBrace, f, Sp, Mid, Sp, And(divides, coprime), CloseBrace)));
    }

    private static Formula Statement()
    {
        var n = F.Id("n");
        return Universal("n", Naturals(),
            Implies(Less(D(0), n),
                Equal(Card(Tuples(n, n)), Card(Divisors(SelfPower(n))))));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), Statement()));

    private static Formula ResultFormula() => Disp(Statement());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
