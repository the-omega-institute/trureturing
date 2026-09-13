using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class FactorialSquareDivisibilityPrimePowerDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower.factorial_square_exact_divisibility_iff_prime_power";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact factorial-square divisibility characterizes prime powers.",
        H("Exact Factorial-Square Divisibility and Prime Powers"),
        Blocks(Describe.Lean(
            DescribeId.Create("a096127-factorial-square-exact-divisibility"),
            DeclarationHandle.Create(Declaration),
            H("The exact exponent is characterized by prime powers"),
            StatementSource.FromAuthor(StatementFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Factorization/murthy2004a096127")),
            Blocks(Paragraph(Text(
                "Legendre's formula converts each factorial divisibility into a prime-valuation "
                + "inequality. Base-p digit-sum submultiplicativity bounds the valuation for "
                + "exponent n+1 and distinguishes exponent n+2 exactly when n is a prime power."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a096127-factorial-square-divisibility-prime-power"),
                ResolutionKind.Proved)))));

    private static Formula StatementFormula()
    {
        Formula n = F.Id("n");
        Formula nFactorial = Factorial(n);
        Formula squareFactorial = Factorial(Power(n, D(2)));
        Formula lower = Divides(Power(Parenthesized(nFactorial), Add(n, D(1))), squareFactorial);
        Formula next = Divides(Power(Parenthesized(nFactorial), Add(n, D(2))), squareFactorial);
        Formula exact = Seq(Parenthesized(lower), Sp, Land, Sp,
            Parenthesized(Seq(Neg, Sp, Parenthesized(next))));
        Formula classification = Seq(Parenthesized(exact), Sp, Iff, Sp,
            Call("IsPrimePow", n));
        return Disp(Seq(Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            D(2), Sp, Le, Sp, n, Sp, Implies, Sp, Parenthesized(classification)));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Factorial(Formula value) => Seq(Parenthesized(value), Bang);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
