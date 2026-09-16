using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class RotatingMemoryFibonacciPeriodCollapseDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/abdelaidoum2026rotatingmemory");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every rational tail Hankel matrix of a rotating-memory Fibonacci sequence is nonsingular.",
        H("Rotating-Memory Tail Hankel Nonsingularity"),
        Blocks(
            Paragraph(Text(
                "The source defines the rotating-memory Fibonacci sequence and proves its "
                    + "period-collapse factor for k at least two. Natural subtraction gives "
                    + "the source convention that negative-index summands contribute zero. "
                    + "Nonsingularity of the arbitrary-size tail Hankel matrix is derived here.")),
            Describe.Lean(
                DescribeId.Create("rotating-memory-definition"),
                DeclarationHandle.Create(Prefix + "rotatingMemory"),
                H("The rotating-memory sequence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The values at zero and one are zero and one. For n at least two, "
                        + "the value is the sum of the preceding 2 plus n modulo k terms. "
                        + "The formal function is total in k; the cited definition assumes "
                        + "k at least one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rotating-memory-period-collapse"),
                DeclarationHandle.Create(Prefix + "period_collapse"),
                H("One full period"),
                StatementSource.FromAuthor(PeriodFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For k at least two and n at least k, advancing by k multiplies the "
                        + "sequence by 3 times 2 to the k minus 2. This is Theorem 1 of "
                        + "the cited paper and supplies the factor for entries on or beyond "
                        + "the Hankel antidiagonal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rotating-memory-tail-hankel-nonsingular"),
                DeclarationHandle.Create(Prefix + "tail_hankel_det_ne_zero"),
                H("Every tail Hankel matrix is nonsingular"),
                StatementSource.FromAuthor(TailHankelFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every k at least two, the k by k matrix with entry R at index "
                        + "k+i+j has nonzero determinant over the rationals. Each entry factors "
                        + "as the positive value R at k, a power of two from each index, and "
                        + "a threshold coefficient equal to one below the antidiagonal and "
                        + "three quarters on or beyond it. Subtracting consecutive threshold "
                        + "rows isolates every positive-index kernel coordinate; the first row "
                        + "then isolates coordinate zero. The source does not state this "
                        + "tail Hankel determinant or full-rank consequence."))),
                DescribeRole.Theorem))));

    private static Formula PeriodFormula() => Disp(ForAll(
        [Natural("k"), Natural("n")],
        Implies(
            AtLeast(D(2), K()),
            Implies(
                AtLeast(K(), N()),
                Equal(
                    R(K(), Add(N(), K())),
                    Multiply(
                        Multiply(D(3), Power(D(2), Subtract(K(), D(2)))),
                        R(K(), N())))))));

    private static Formula TailHankelFormula()
    {
        var entry = Rat(R(K(), Add(Add(K(), I()), J())));
        var matrix = Seq(
            Parenthesized(entry),
            Underscore,
            Grp(Seq(I(), Comma, Sp, J(), Sp, InMacro, Sp, Call("Fin", K()))));
        return Disp(ForAll(
            [Natural("k")],
            Implies(
                AtLeast(D(2), K()),
                new Formula.Relation(
                    Call("det", matrix), FormulaRelationOperator.NotEqual, D(0)))));
    }

    private static Formula K() => F.Id("k");
    private static Formula N() => F.Id("n");
    private static Formula I() => F.Id("i");
    private static Formula J() => F.Id("j");
    private static Formula R(Formula period, Formula index) =>
        Call("rotatingMemory", period, index);
    private static Formula Rat(Formula value) => Call("Rat", value);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtLeast(Formula lower, Formula upper) =>
        new Formula.Relation(lower, FormulaRelationOperator.LessThanOrEqual, upper);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula.BoundVariable Natural(string name) =>
        new(FormulaIdentifier.Create(name), Naturals());
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
