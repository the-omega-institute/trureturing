using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class PudelkoFibonacciMinimumLimitRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/PudelkoFibonacciMinimumLimitRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/pudelko2025modular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform count bound refutes the proposed one-quarter limit for Fibonacci minima.",
        H("Fibonacci Minima Under Bounded Initialization"),
        Blocks(
            Node(
                "bilateral-fibonacci",
                "The bilateral Fibonacci sequence",
                "bilateral_fibonacci",
                BilateralFibonacciFormula(),
                "For integer initial values x and y, this closed form has value x at index "
                    + "zero and y at index one. It satisfies a(k+2)=a(k+1)+a(k) for every "
                    + "integer k, so negative and positive indices belong to one bilateral "
                    + "recurrence. The notation bilateralFibonacci is the canonical "
                    + "underscore-free rendering of bilateral_fibonacci.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "minimum-at-zero",
                "A global minimum at position zero",
                "min0",
                MinimumAtZeroFormula(),
                "The predicate allows ties: position zero need only be one global minimizer "
                    + "of the absolute values. The quantifier ranges over every integer index, "
                    + "rather than a finite observation window.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "bounded-minimum-probability",
                "The bounded-initialization probability",
                "bounded_min0_probability",
                BoundedProbabilityFormula(),
                "The numerator counts integer pairs in the inclusive square [-N,N]^2 for "
                    + "which zero is a global minimizer. The denominator is the square's "
                    + "cardinality (2N+1)^2, and both quantities are coerced to rational "
                    + "numbers before division.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "one-quarter-limit-claim",
                "The proposed one-quarter limit",
                "claim",
                ClaimFormula(),
                "This is the epsilon-threshold form of convergence of the bounded probability "
                    + "to one quarter. It is the bounded-initialization reading of the paper's "
                    + "formula at minimum position zero for the Fibonacci recurrence.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "one-quarter-limit-refutation",
                "The proposed limit is false",
                "result",
                ResultFormula(),
                "For t at least three, the count bound gives probability at most 2/9, which "
                    + "is separated from 1/4 by more than 1/72. After any proposed threshold, "
                    + "choosing t as the maximum of three and that threshold supplies a later "
                    + "index N=6t and contradicts the required epsilon bound.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "pudelko-fibonacci-minimum-limit-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("pudelko-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula BilateralFibonacciFormula()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var k = F.Id("k");
        return Disp(ForAll(
            [Bound("x", Integers()), Bound("y", Integers()), Bound("k", Integers())],
            Equal(
                Call("bilateralFibonacci", x, y, k),
                Add(
                    Multiply(x, Apply(Seq(F.Id("Int"), Dot, F.Id("fib")),
                        Subtract(k, D(1)))),
                    Multiply(y, Apply(Seq(F.Id("Int"), Dot, F.Id("fib")), k))))));
    }

    private static Formula MinimumAtZeroFormula()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var k = F.Id("k");
        var condition = ForAll(
            [Bound("k", Integers())],
            AtMost(
                new Formula.Absolute(Call("bilateralFibonacci", x, y, D(0))),
                new Formula.Absolute(Call("bilateralFibonacci", x, y, k))));
        return Disp(ForAll(
            [Bound("x", Integers()), Bound("y", Integers())],
            Iff(Call("min0", x, y), Parenthesized(condition))));
    }

    private static Formula BoundedProbabilityFormula()
    {
        var n = F.Id("N");
        var denominator = new Formula.Power(
            RationalCast(Add(Multiply(D(2), n), D(1))), D(2));
        return Disp(ForAll(
            [Bound("N", Naturals())],
            Equal(
                Call("boundedMin0Probability", n),
                new Formula.Fraction(RationalCast(GoodCardinality(n)), denominator))));
    }

    private static Formula ClaimFormula()
    {
        var epsilon = F.Id("epsilon");
        var threshold = F.Id("Nzero");
        var n = F.Id("N");
        var close = Less(
            new Formula.Absolute(Subtract(
                Call("boundedMin0Probability", n),
                new Formula.Fraction(D(1), D(4)))),
            epsilon);
        var eventually = Exists(
            [Bound("Nzero", Naturals())],
            ForAll(
                [Bound("N", Naturals())],
                Implies(AtMost(threshold, n), Parenthesized(close))));
        var limit = ForAll(
            [Bound("epsilon", Rationals())],
            Implies(Less(D(0), epsilon), Parenthesized(eventually)));
        return Disp(Iff(F.Id("claim"), Parenthesized(limit)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula GoodCardinality(Formula n)
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var nz = IntegerCast(n);
        var constraints = And(
            AtMost(new Formula.Negate(nz), x),
            AtMost(x, nz),
            AtMost(new Formula.Negate(nz), y),
            AtMost(y, nz),
            Call("min0", x, y));
        var set = Seq(
            OpenBrace,
            Parenthesized(Seq(x, Comma, Sp, y)),
            Sp, InMacro, Sp,
            new Formula.Power(Integers(), D(2)),
            Sp, Mid, Sp,
            Parenthesized(constraints),
            CloseBrace);
        return new Formula.Absolute(set);
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));

    private static Formula IntegerCast(Formula value) =>
        Parenthesized(Seq(value, Colon, Sp, Integers()));

    private static Formula RationalCast(Formula value) =>
        Parenthesized(Seq(value, Colon, Sp, Rationals()));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(
                Parenthesized(clauses[index]),
                FormulaLogicOperator.And,
                result);
        }
        return result;
    }
}
