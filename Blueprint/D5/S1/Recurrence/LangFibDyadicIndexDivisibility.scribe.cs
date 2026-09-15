using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class LangFibDyadicIndexDivisibilityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/LangFibDyadicIndexDivisibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibonacci numbers at Lang's dyadic indices have the conjectured power-of-two divisor.",
        H("Dyadic Divisibility at Lang's Fibonacci Indices"),
        Blocks(
            Paragraph(Text(
                "The parameters n and m are natural numbers. Nat.fib is the Fibonacci "
                    + "sequence with Nat.fib(0)=0 and Nat.fib(1)=1. The symbol ∣ denotes divisibility in the natural "
                    + "numbers; multiplication and powers are natural-number operations. "
                    + "The subtraction n-2 is truncated natural subtraction, which agrees "
                    + "with ordinary subtraction under 3<=n. Only the first sentence of "
                    + "the A319197 comment is settled here. The product "
                    + "A(n)=Product_{j=3..n} a(j), the I(n; m) factorization conjecture, "
                    + "and the specific factors from A049660 and A253368 are not claimed.")),
            Describe.Lean(
                DescribeId.Create("a319197-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The dyadic divisibility conjecture"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Recurrence/lang2018a319197")),
                Blocks(Paragraph(Text(
                    "At n=3, Nat.fib(6)=8 and Fibonacci divisibility carries the factor 8 "
                        + "to Nat.fib(6m). Each increment of n doubles the index. The Fibonacci "
                        + "doubling identity expresses the new value as the old value "
                        + "times an even cofactor, so induction supplies one further "
                        + "factor of 2 at every step. Since 2^n is positive, divisibility "
                        + "gives the nonnegative-integral quotient in the quoted comment."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a319197-lang-fib-dyadic-index-divisibility"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var index = Multiply(
            Multiply(new Formula.Power(D(2), Parenthesized(Subtract(n, D(2)))), D(3)),
            m);
        var fibonacci = new Formula.Apply(Seq(Operatorname, Grp(F.Id("Nat"), Dot, F.Id("fib"))), [index]);
        var hypothesis = new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual, n);
        var conclusion = new Formula.Relation(
            new Formula.Power(D(2), n), FormulaRelationOperator.Divides, fibonacci);
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals()),
                new Formula.BoundVariable(FormulaIdentifier.Create("m"), Naturals()),
            ],
            new Formula.Logic(
                Parenthesized(hypothesis), FormulaLogicOperator.Implies,
                Parenthesized(conclusion))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
