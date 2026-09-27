using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Turan;

internal sealed class StrictlyIncreasingTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Turan/StrictlyIncreasingTail.";
    private static readonly LibraryNoteRef Krasikov =
        LibraryNoteRef.Create("D5/L/Recurrence/krasikov2011turan");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict off-diagonal increase and monotone diagonal give a weighted Turan bound on the complete closed right tail.",
        H("A Weighted Turan Tail for Increasing Recurrences"),
        Blocks(
            Paragraph(Text("The sequence uses q(0)=1, q(1)=(t-b(0))/a(1), and "
                + "a(j+2)q(j+2)=(t-b(j+1))q(j+1)-a(j+1)q(j). "
                + "The theorem requires a(0)=0, strict increase of a, and monotonicity of b. "
                + "Its conclusion applies to every n at least one and every t at or to the right "
                + "of b(n)-2a(n). The coefficient of the neighbor product is a(n+1)/a(n), "
                + "which is greater than one; this is a weighted, non-strict conclusion.")),
            Describe.Lean(
                DescribeId.Create("turan-orthonormal"),
                DeclarationHandle.Create(Prefix + "orthonormal"),
                H("The canonical unit-normalized recurrence"),
                StatementSource.FromAuthor(RecurrenceFormula()),
                AssessedProvenance.FromRepo(Krasikov),
                Blocks(Paragraph(Text("This is the actual c=1 recurrence, with initial value one. "
                    + "The coefficients a and b are arbitrary real sequences; positivity enters "
                    + "through the theorem hypotheses rather than the definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("turan-weighted-tail"),
                DeclarationHandle.Create(Prefix + "weighted_turan_nonneg_of_strict_mono"),
                H("Weighted nonnegativity on the right tail"),
                StatementSource.FromAuthor(TailFormula()),
                AssessedProvenance.FromRepo(Krasikov),
                Blocks(Paragraph(Text("The base case scales the determinant to a nonnegative square. "
                    + "The central range is a sum of squares with nonnegative coefficient. "
                    + "In the farther right tail, strong induction compares successive weighted "
                    + "determinants through a positive factor; the residual quadratic is "
                    + "nonnegative because its discriminant factors as a strictly negative "
                    + "product under strict growth of a. This is live content beyond an "
                    + "instance of the published theorem. GStrict and VTail call this result "
                    + "directly and separately obtain strict unweighted inequalities."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula EqF(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Q(Formula index) => Call("q", index);
    private static Formula A(Formula index) => Call("a", index);
    private static Formula B(Formula index) => Call("b", index);

    private static Formula RecurrenceFormula()
    {
        var j = F.Id("j");
        var t = F.Id("t");
        var next = Add(j, D(1));
        var next2 = Add(j, D(2));
        return Disp(new Formula.Aligned([
            EqF(Q(D(0)), D(1)),
            EqF(Q(D(1)), Div(Sub(t, B(D(0))), A(D(1)))),
            EqF(Mul(A(next2), Q(next2)),
                Sub(Mul(Sub(t, B(next)), Q(next)), Mul(A(next), Q(j))))
        ]));
    }

    private static Formula TailFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var t = F.Id("t");
        var n = F.Id("n");
        var next = Add(n, D(1));
        var prev = Sub(n, D(1));
        Formula O(Formula index) => Call("orthonormal", a, b, t, index);
        var determinant = Sub(new Formula.Power(O(n), D(2)),
            Mul(Mul(Div(A(next), A(n)), O(prev)), O(next)));
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        return Disp(Seq(Forall, Sp, a, Comma, Sp, b, Colon, Sp,
            new Formula.TypeArrow(naturals, reals), Comma, Sp,
            t, Colon, Sp, reals, Comma, Sp,
            EqF(A(D(0)), D(0)), Sp, Rightarrow, Sp,
            Call("StrictMono", a), Sp, Rightarrow, Sp,
            Call("Monotone", b), Sp, Rightarrow, Sp,
            Forall, Sp, n, Colon, Sp, naturals, Comma, Sp,
            D(1), Sp, Le, Sp, n, Sp, Rightarrow, Sp,
            new Formula.Relation(Sub(B(n), Mul(D(2), A(n))),
                FormulaRelationOperator.LessThanOrEqual, t), Sp, Rightarrow, Sp,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, determinant)));
    }
}
