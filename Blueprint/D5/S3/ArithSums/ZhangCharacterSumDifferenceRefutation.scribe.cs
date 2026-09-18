using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class ZhangCharacterSumDifferenceRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/zhang2025problems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two quadratic-polynomial Legendre sums differ by one for every odd prime.",
        H("A Constant-One Difference of Polynomial Character Sums"),
        Blocks(
            Paragraph(Text(
                "The Legendre symbol notation and the range from one through p-1 are those of "
                    + "identity (2). The paper's preceding corollary quantifies over odd primes.")),
            Node(
                "characterSum",
                "The polynomial Legendre character sum",
                CharacterSumFormula(),
                "For a prime p and an integer-coefficient polynomial f, this is the sum "
                    + "of the Legendre symbols of f(x) over the integers from one through p-1.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "FundamentallyDifferent",
                "Fundamental difference on the summation domain",
                FundamentallyDifferentFormula(),
                "The two symbol-valued functions are different when some x in the same finite "
                    + "summation domain gives unequal values. This is equivalent to inequality "
                    + "of those functions on that domain.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "claim",
                "The constant-value assertion in Question (D)",
                ClaimFormula(),
                "Question (B) asks: \"Whether there are infinitely many pairs of fundamentally "
                    + "different integer coefficients polynomials f(x) and g(x) (That is, "
                    + "(f(x)/p) ≠ (g(x)/p)) such that Σ_{x=1}^{p−1} (f(x)/p) − "
                    + "Σ_{x=1}^{p−1} (g(x)/p) = c, (2) where c is a fixed constant.\" "
                    + "Question (D) asks: \"Whether the values of c can only be 0 or 2?\" "
                    + "Identity (2) does not print an explicit universal binder for p. Here one "
                    + "integer c is bound outside the universal odd-prime condition, following "
                    + "the preceding corollary. Thus the same c is the difference for every odd "
                    + "prime, and the two symbol functions differ at every such prime.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "result",
                "A constant-one counterexample",
                Disp(new Formula.Not(F.Id("claim"))),
                "Take f(X)=X^2 and g(X)=(X+1)^2. For every odd prime p, the first "
                    + "sum is p-1. The second is p-2 because its final term, at x=p-1, "
                    + "is zero and every earlier term is one. At that same endpoint the first "
                    + "symbol is one, so the functions differ. Their sum difference is the fixed "
                    + "integer c=1, which is neither zero nor two.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("zhang-character-sum-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        provenance,
        Blocks(Paragraph(Text(prose))),
        role);

    private static Formula CharacterSumFormula()
    {
        var p = F.Id("p");
        var f = F.Id("f");
        var x = F.Id("x");
        var equation = Equal(Call("characterSum", p, f), BoundedCharacterSum(p, f, x));
        return UniversalPrimePolynomial(p, f, equation);
    }

    private static Formula FundamentallyDifferentFormula()
    {
        var p = F.Id("p");
        var f = F.Id("f");
        var g = F.Id("g");
        var x = F.Id("x");
        var interval = And(
            LessThanOrEqual(D(1), x),
            LessThan(x, p));
        var unequal = NotEqual(Legendre(p, f, x), Legendre(p, g, x));
        var exists = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("x"),
            Naturals(),
            And(interval, unequal));
        var equation = Iff(
            Call("FundamentallyDifferent", p, f, g),
            exists);
        return UniversalPrimePolynomials(p, f, g, equation);
    }

    private static Formula ClaimFormula()
    {
        var p = F.Id("p");
        var f = F.Id("f");
        var g = F.Id("g");
        var c = F.Id("c");
        var oddPrime = And(Call("Prime", p), NotEqual(p, D(2)));
        var perPrime = And(
            Call("FundamentallyDifferent", p, f, g),
            Equal(
                Subtract(Call("characterSum", p, f), Call("characterSum", p, g)),
                c));
        var allPrimes = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("p"),
            Naturals(),
            Implies(oddPrime, perPrime));
        var values = Or(Equal(c, D(0)), Equal(c, D(2)));
        var body = Implies(allPrimes, values);
        var quantified = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("f"), Polynomials()),
                new Formula.BoundVariable(FormulaIdentifier.Create("g"), Polynomials()),
                new Formula.BoundVariable(FormulaIdentifier.Create("c"), Integers())
            ],
            body);
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula UniversalPrimePolynomial(
        Formula p,
        Formula f,
        Formula body) => Disp(new Formula.Bind(
        FormulaQuantifier.ForAll,
        FormulaIdentifier.Create("p"),
        Naturals(),
        Implies(Call("Prime", p), new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("f"),
            Polynomials(),
            body))));

    private static Formula UniversalPrimePolynomials(
        Formula p,
        Formula f,
        Formula g,
        Formula body) => Disp(new Formula.Bind(
        FormulaQuantifier.ForAll,
        FormulaIdentifier.Create("p"),
        Naturals(),
        Implies(Call("Prime", p), new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("f"), Polynomials()),
                new Formula.BoundVariable(FormulaIdentifier.Create("g"), Polynomials())
            ],
            body))));

    private static Formula BoundedCharacterSum(Formula p, Formula polynomial, Formula x) => Seq(
        new Formula.Subscript(Sum, Seq(x, Sp, Eq, Sp, D(1))),
        Caret,
        Grp(Subtract(p, D(1))),
        Sp,
        Legendre(p, polynomial, x));

    private static Formula Legendre(Formula p, Formula polynomial, Formula x) =>
        Parenthesized(new Formula.Fraction(new Formula.Apply(polynomial, [IntegerCast(x)]), p));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Polynomials() =>
        Seq(Mathbb, Grp(F.Id("Z")), OpenBracket, F.Id("X"), CloseBracket);

    private static Formula Integers() => new Formula.Integers();

    private static Formula IntegerCast(Formula value) =>
        Parenthesized(Seq(value, Colon, Sp, Integers()));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
