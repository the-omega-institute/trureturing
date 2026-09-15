using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class StephanTriangleSecondColumnDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/StephanTriangleSecondColumn.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/kimberling2004a054096");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second column of Kimberling's row-sum triangle is A006183 shifted right.",
        H("Stephan's A054096 Second-Column Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a054096-row-sum"),
                DeclarationHandle.Create(Prefix + "rowSum"),
                H("Finite row sum"),
                StatementSource.FromAuthor(RowSumFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a triangle T and a natural row index n, rowSum(T,n) is the "
                        + "sum of T(n,k) over all column indices k from zero through n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a054096-triangle-equations"),
                DeclarationHandle.Create(Prefix + "IsA054090Triangle"),
                H("The A054090 triangle equations"),
                StatementSource.FromAuthor(TriangleFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The zeroth entry of every row is one. The first entry of row n+1 "
                        + "is the sum of row n. For columns k from two through n, the "
                        + "next entry is obtained from the preceding entry by subtracting "
                        + "(-1)^k times the sum of row n-k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a054096-shifted-a006183"),
                DeclarationHandle.Create(Prefix + "IsShiftedA006183"),
                H("The shifted A006183 recurrence"),
                StatementSource.FromAuthor(ShiftedFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The offset-one sequence A006183 becomes B(1)=1 and B(2)=2 after "
                        + "the shift. For every j at least three, its recurrence is "
                        + "B(j)=j B(j-1)+(3-j) B(j-2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a054096-row-sum-successor"),
                DeclarationHandle.Create(Prefix + "rowSum_succ"),
                H("Row-sum invariant"),
                StatementSource.FromAuthor(RowSumSuccessorFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Every triangle satisfying the A054090 equations has "
                        + "rowSum(T,n+1)=n rowSum(T,n)+2. A cross-row induction relates "
                        + "adjacent rows, and summing those relations telescopes across "
                        + "the row. Its standalone statement allows subsequent results "
                        + "about other columns and the row-sum sequence to use it directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a054096-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Stephan's second-column conjecture"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every A054090 triangle T and every shifted A006183 sequence B, "
                        + "the second-column value T(n,2) equals B(n-1) for every n at "
                        + "least two. The cross-row induction yields the row-sum invariant; "
                        + "a telescoping step identifies T(n,2) with a difference of "
                        + "successive row sums, and a final induction matches that difference "
                        + "to the shifted recurrence."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a054096-stephan-triangle-second-column"),
                    ResolutionKind.Proved)))));

    private static Formula RowSumFormula()
    {
        Formula t = F.Id("T");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        return Disp(ForAll(
            [Bound("T", TriangleType()), Bound("n", Naturals())],
            Equal(RowSum(t, n), FiniteSum(k, n, Entry(t, n, k)))));
    }

    private static Formula TriangleFormula()
    {
        Formula t = F.Id("T");
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula j = F.Id("j");
        Formula zeroColumn = ForAll(
            [Bound("n", Naturals())], Equal(Entry(t, n, D(0)), D(1)));
        Formula firstColumn = ForAll(
            [Bound("n", Naturals())],
            Equal(
                Entry(t, Add(n, D(1)), D(1)),
                FiniteSum(j, n, Entry(t, n, j))));
        Formula recurrence = ForAll(
            [Bound("n", Naturals()), Bound("k", Naturals())],
            Implies(
                And(LessOrEqual(D(2), k), LessOrEqual(k, n)),
                Equal(
                    Entry(t, n, k),
                    Subtract(
                        Entry(t, n, Subtract(k, D(1))),
                        Multiply(
                            new Formula.Power(
                                Parenthesized(new Formula.Negate(D(1))), k),
                            FiniteSum(
                                j,
                                Subtract(n, k),
                                Entry(t, Subtract(n, k), j)))))));
        return Disp(ForAll(
            [Bound("T", TriangleType())],
            Iff(
                Call("IsA054090Triangle", t),
                And(zeroColumn, And(firstColumn, recurrence)))));
    }

    private static Formula ShiftedFormula()
    {
        Formula b = F.Id("B");
        Formula j = F.Id("j");
        Formula initialOne = Equal(Entry(b, D(1)), D(1));
        Formula initialTwo = Equal(Entry(b, D(2)), D(2));
        Formula recurrence = ForAll(
            [Bound("j", Naturals())],
            Implies(
                LessOrEqual(D(3), j),
                Equal(
                    Entry(b, j),
                    Add(
                        Multiply(j, Entry(b, Subtract(j, D(1)))),
                        Multiply(
                            Parenthesized(Subtract(D(3), j)),
                            Entry(b, Subtract(j, D(2))))))));
        return Disp(ForAll(
            [Bound("B", SequenceType())],
            Iff(
                Call("IsShiftedA006183", b),
                And(initialOne, And(initialTwo, recurrence)))));
    }

    private static Formula RowSumSuccessorFormula()
    {
        Formula t = F.Id("T");
        Formula n = F.Id("n");
        return Disp(ForAll(
            [Bound("T", TriangleType()), Bound("n", Naturals())],
            Implies(
                Call("IsA054090Triangle", t),
                Equal(
                    RowSum(t, Add(n, D(1))),
                    Add(Multiply(n, RowSum(t, n)), D(2))))));
    }

    private static Formula ResultFormula()
    {
        Formula t = F.Id("T");
        Formula b = F.Id("B");
        Formula n = F.Id("n");
        return Disp(ForAll(
            [Bound("T", TriangleType()), Bound("B", SequenceType())],
            Implies(
                And(
                    Call("IsA054090Triangle", t),
                    Call("IsShiftedA006183", b)),
                ForAll(
                    [Bound("n", Naturals())],
                    Implies(
                        LessOrEqual(D(2), n),
                        Equal(
                            Entry(t, n, D(2)),
                            Entry(b, Subtract(n, D(1)))))))));
    }

    private static Formula FiniteSum(Formula index, Formula upper, Formula summand) =>
        Seq(
            F.Sum,
            Underscore,
            Grp(index, Sp, Eq, Sp, D(0)),
            Caret,
            Grp(upper),
            Sp,
            summand);

    private static Formula RowSum(Formula triangle, Formula row) =>
        Call("rowSum", triangle, row);

    private static Formula Entry(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula TriangleType() =>
        new Formula.TypeArrow(Naturals(), new Formula.TypeArrow(Naturals(), Integers()));

    private static Formula SequenceType() =>
        new Formula.TypeArrow(Naturals(), Integers());

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Integers() => new Formula.Integers();

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
