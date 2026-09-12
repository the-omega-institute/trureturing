using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class FactorialNestedReciprocalSumRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/FactorialNestedReciprocalSumRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/mathar2014a093345");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The factorial nested reciprocal sum satisfies Mathar's third-order recurrence.",
        H("The Factorial Nested Reciprocal Sum of OEIS A093345"),
        Blocks(
            Paragraph(Text("All indices are natural numbers, and a takes values in the rationals. "
                + "Factorials and indices appearing as coefficients are cast to the rationals. "
                + "Division and coefficient subtraction are rational operations; subtraction "
                + "in the indices is natural subtraction. The hypothesis n >= 3 prevents "
                + "truncation in the three preceding indices.")),
            Node("a", "The factorial nested reciprocal sum", DefinitionFormula(),
                "The factor n! multiplies one plus the outer sum over i from 1 to n. "
                + "Its ith summand is 1/i times the inner sum over j from 0 to i-1 of 1/j!. "
                + "This is a rational-valued definition; integrality is not assumed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mathar_a093345", "Mathar's third-order recurrence", RecurrenceFormula(),
                "For the auxiliary prefix b(m)=m! times the sum of 1/j! over 0 <= j <= m, "
                + "the factorial successor identity gives b(m+1)=(m+1)b(m)+1. "
                + "The final outer summand gives a(m+1)=(m+1)a(m)+b(m). "
                + "Three consecutive updates for a and two for b eliminate the prefix, "
                + "and rational algebra yields the recurrence for every n at least three.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a093345-factorial-nested-reciprocal-sum-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a093345-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var j = F.Id("j");
        var inner = Summation(j, D(0), Subtract(i, D(1)),
            new Formula.Fraction(D(1), Factorial(j)));
        var outer = Summation(i, D(1), n,
            Multiply(new Formula.Fraction(D(1), i), inner));
        return Universal(Equal(A(n), Multiply(Factorial(n), Parenthesized(Add(D(1), outer)))));
    }

    private static Formula RecurrenceFormula()
    {
        var n = F.Id("n");
        var lhs = Subtract(Add(Subtract(A(n), Multiply(Multiply(D(2), n),
                A(Subtract(n, D(1))))),
            Multiply(Parenthesized(Subtract(Power(n, D(2)), D(2))), A(Subtract(n, D(2))))),
            Multiply(Power(Parenthesized(Subtract(n, D(2))), D(2)), A(Subtract(n, D(3)))));
        return Universal(Seq(D(3), Sp, Le, Sp, n, Sp, Implies, Sp, Equal(lhs, D(0))));
    }

    private static Formula Universal(Formula body) => Disp(Seq(
        Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp, body));
    private static Formula Summation(Formula index, Formula lower, Formula upper, Formula body) =>
        Seq(F.Sum, Underscore, Grp(index, Sp, Eq, Sp, lower),
            Caret, Grp(upper), Sp, Parenthesized(body));
    private static Formula A(Formula index) => new Formula.Apply(F.Id("a"), [index]);
    private static Formula Factorial(Formula value) => Seq(value, Bang);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
}
