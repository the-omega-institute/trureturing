using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class SchulteFactorialSquarePrimeCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/schulte2020a006472");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's A006472 divisibility condition characterizes prime natural numbers.",
        H("Schulte's Factorial-Square Prime Criterion"),
        Blocks(
            Paragraph(Text(
                "All variables and values lie in the natural numbers N, including zero. "
                    + "The symbol m is the sequence index, n is the criterion input, and a "
                    + "denotes A006472. The operator factorial(x) is x!, powers and products "
                    + "are natural-number operations, subtraction is truncated at zero, and "
                    + "the slash is exact natural-number division. The symbol ∣ denotes "
                    + "natural divisibility, and Prime(n) means that n is prime. Only the "
                    + "Conjecture sentence in Werner Schulte's 2020 comment is settled, for "
                    + "every n at least 2. The proof establishes that every composite n at "
                    + "least 9 divides a(n-1), while the composite cases n < 9 (n = 4, 6, 8) are checked directly. Its "
                    + "odd branch reuses the frozen theorem "
                    + "factorial_dvd_triangular_of_not_odd_prime; the even branch uses "
                    + "double-factorial identities and two-adic quotient bookkeeping.")),
            Node(
                "a",
                "The A006472 sequence",
                DefinitionFormula(),
                "For each natural m, a(m) is the exact natural quotient of "
                    + "factorial(m) times factorial(m-1) by 2^(m-1). The exactness follows "
                    + "by splitting the required powers of two between the two factorials.",
                DescribeRole.Definition),
            Node(
                "result",
                "Schulte's primality criterion",
                ResultFormula(),
                "For every natural n at least 2, n divides 2 times a(n-1) plus 4 exactly "
                    + "when n is prime. For primes, Wilson's theorem and Fermat's theorem "
                    + "evaluate the scaled expression modulo n. For composite n at least 9, "
                    + "divisibility of a(n-1) forces any divisibility of the displayed sum to "
                    + "make n divide 4, which is impossible; the smaller composite cases are "
                    + "checked directly.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a006472-schulte-factorial-square-prime-criterion"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(
            DescribeId.Create("a006472-" + name),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))),
            role,
            claim);

    private static Formula DefinitionFormula()
    {
        var mIdentifier = FormulaIdentifier.Create("m");
        var m = new Formula.LatexWord(mIdentifier);
        var predecessor = Subtract(m, D(1));
        var numerator = Multiply(
            Call("factorial", m),
            Call("factorial", predecessor));
        var denominator = Power(D(2), predecessor);
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            mIdentifier,
            Naturals(),
            Equal(Call("a", m), NaturalDivide(numerator, denominator))));
    }

    private static Formula ResultFormula()
    {
        var nIdentifier = FormulaIdentifier.Create("n");
        var n = new Formula.LatexWord(nIdentifier);
        var predecessor = Subtract(n, D(1));
        var divisibility = Divides(
            n,
            Add(Multiply(D(2), Call("a", predecessor)), D(4)));
        var criterion = Iff(
            Parenthesized(divisibility),
            Parenthesized(Call("Prime", n)));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            nIdentifier,
            Naturals(),
            Implies(
                Parenthesized(LessOrEqual(D(2), n)),
                Parenthesized(criterion))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula NaturalDivide(Formula numerator, Formula denominator) =>
        Seq(Parenthesized(numerator), Sp, Slash, Sp, Parenthesized(denominator));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
