using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class CloitreSquareRootPrimeGapRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeGaps/CloitreSquareRootPrimeGapRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/cloitre2003a079063");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime counting refutes the eventual square-root lower bound proposed for A079063.",
        H("The OEIS A079063 Square-Root Lower-Bound Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a079063-least-prime-gap-index"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The least square-root prime-gap index"),
                StatementSource.FromAuthor(AFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Here prime(n) is the n-th prime, represented as Nat.nth Nat.Prime "
                        + "(n-1). For n at least one the witness set is nonempty, so sInf "
                        + "is its least member. If the set is empty, the natural-number "
                        + "convention sInf empty equals zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a079063-eventual-lower-bound"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The eventual positive square-root lower bound"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the weakest quantified reading of the conjecture: some "
                        + "positive real constant bounds a(n) strictly below by c times "
                        + "the square root of n for every sufficiently large natural n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a079063-eventual-lower-bound-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The eventual lower bound is false"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A local one-unit square-root increment bound is iterated over blocks "
                        + "of length 3r^2 to obtain a linear upper bound for square roots "
                        + "of quadratic-index primes. The resulting quadratic lower bound "
                        + "on prime counting contradicts the Chebyshev upper bound."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a079063-sqrt-prime-gap-lower-bound-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula AFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var firstIndex = Subtract(Add(n, k), D(1));
        var baseIndex = Subtract(n, D(1));
        var gap = Subtract(SquareRoot(NthPrime(firstIndex)), SquareRoot(NthPrime(baseIndex)));
        var condition = And(Less(D(0), k), Less(D(1), gap));
        var witnesses = Seq(
            OpenBrace, k, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            Parenthesized(condition), CloseBrace);
        return Disp(ForAll("n", Naturals(),
            Equal(Call("a", n), Call("sInf", witnesses))));
    }

    private static Formula ClaimFormula()
    {
        var c = F.Id("c");
        var n = F.Id("n");
        var cutoff = F.Id("N");
        var lowerBound = Less(
            Multiply(c, SquareRoot(Coerce(n, Reals()))),
            Coerce(Call("a", n), Reals()));
        var tail = ForAll("n", Naturals(),
            Implies(AtMost(cutoff, n), lowerBound));
        var body = Exists("c", Reals(),
            And(Less(D(0), c), Exists("N", Naturals(), tail)));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula NthPrime(Formula index) =>
        Call("nth", F.Id("Prime"), index);

    private static Formula SquareRoot(Formula value) =>
        Call("sqrt", value);

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Reals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Real"));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And,
            Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
}
