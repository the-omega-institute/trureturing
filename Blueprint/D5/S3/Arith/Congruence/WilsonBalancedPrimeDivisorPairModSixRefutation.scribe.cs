using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class WilsonBalancedPrimeDivisorPairModSixRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/WilsonBalancedPrimeDivisorPairModSixRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/wilson2015a260310");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The balanced pair (140140, 141601) refutes Wilson's mod-six conjecture for OEIS A260310.",
        H("The OEIS A260310 Balanced Prime-Divisor Pair Conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("a260310-distinct-prime-divisor-sum"),
                DeclarationHandle.Create(Prefix + "S"),
                H("The distinct prime-divisor sum"),
                StatementSource.FromAuthor(SFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural n, S(n) is the sum of the distinct prime divisors "
                        + "in Nat.primeFactors(n). This is OEIS A008472."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a260310-balanced-pair"),
                DeclarationHandle.Create(Prefix + "IsPair"),
                H("Balanced pairs"),
                StatementSource.FromAuthor(IsPairFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The frozen definition "
                        + "D5/S3/PrimeForms/PrimaryPseudoperfectPorts.squarefreeDeriv "
                        + "is the sum, over each distinct prime divisor p of n, of the "
                        + "natural-number quotient n divided by p (OEIS A069359). A pair "
                        + "has its smaller member first, has equal combined S and "
                        + "squarefreeDeriv values, has unequal S values, and excludes the "
                        + "equality S(y) = squarefreeDeriv(y). These are the textual and "
                        + "program filters used by the entry."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a260310-mod-six-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Wilson's mod-six conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every balanced pair of natural numbers, the conjecture says that a "
                        + "composite smaller member greater than one is divisible by six."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a260310-mod-six-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The mod-six conjecture fails"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The pair is (140140, 141601). Here 140140 = 2^2 * 5 * 7^2 * 11 * 13 "
                        + "and is congruent to 4 modulo 6, while 141601 is prime. The values "
                        + "S(140140) = 38, squarefreeDeriv(140140) = 141638, "
                        + "S(141601) = 141601, and squarefreeDeriv(141601) = 1 establish "
                        + "the balance and filters. Minimality and the prime/composite "
                        + "alternation sentence are not claimed."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a260310-balanced-prime-divisor-pair-mod-six-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula SFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            Equal(Call("S", n), SumOverPrimeFactors(p, n, p))));
    }

    private static Formula IsPairFormula()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var body = Iff(
            Call("IsPair", x, y),
            And(
                Relation(x, FormulaRelationOperator.LessThan, y),
                Equal(Add(Call("S", x), Call("S", y)),
                    Add(Call("squarefreeDeriv", x), Call("squarefreeDeriv", y))),
                Relation(Call("S", x), FormulaRelationOperator.NotEqual, Call("S", y)),
                Relation(Call("S", y), FormulaRelationOperator.NotEqual,
                    Call("squarefreeDeriv", y))));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("y"), Naturals()),
            ],
            body));
    }

    private static Formula ClaimFormula()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var quantified = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("y"), Naturals()),
            ],
            Implies(Call("IsPair", x, y),
                Implies(Relation(D(1), FormulaRelationOperator.LessThan, x),
                    Implies(new Formula.Not(Prime(x)),
                        Relation(D(6), FormulaRelationOperator.Divides, x)))));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula SumOverPrimeFactors(
        Formula prime,
        Formula n,
        Formula summand) =>
        Seq(Sum, Underscore,
            Grp(prime, Sp, InMacro, Sp, PrimeFactors(n)), Sp, summand);

    private static Formula PrimeFactors(Formula n) =>
        Seq(Operatorname, Grp(F.Id("primeFactors")), Open, n, Close);

    private static Formula Prime(Formula n) =>
        Seq(Operatorname, Grp(F.Id("Prime")), Open, n, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator relation,
        Formula right) => new Formula.Relation(left, relation, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
