using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Sun;

internal sealed class VStrictDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Sun =
        LibraryNoteRef.Create("D5/L/Recurrence/sun2026generalizations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second complete closed-domain clause of Sun's Conjecture 5.2 holds at every positive index.",
        H("Strict Turan Inequality for v"),
        Blocks(Describe.Lean(
            DescribeId.Create("sun-v-strict-turan"),
            DeclarationHandle.Create("D5/S1/Recurrence/Sun/VStrict.v_strict_turan"),
            H("The full v inequality on x at most -1/8"), StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(Sun),
            Blocks(Paragraph(Text("For every n at least one and every real x at most -1/8, "
                + "the square of v(x,n) strictly exceeds the product of its two neighbors. "
                + "Set t=-x, m=n(n+1), D=4m+1, r=2m sqrt(m)/sqrt(D), "
                + "L=m-r, U=m+r, and T=m-2n^3/sqrt(4n^2-1). "
                + "The exact identity 4m^3-(m-1/8)^2 D=(12m-1)/64>0 proves "
                + "L<1/8; also T<m<U. Thus t at least 1/8 and t<T lies in "
                + "the open local interval (L,U), where the recurrence determinant "
                + "is a positive quadratic form. Positive recurrence coefficients "
                + "exclude adjacent zeros. At t at least T, VTail supplies strictness "
                + "including the threshold. The proof translates the sign-normalized "
                + "determinant back to literal lowercase v. The argument includes "
                + "x=-1/8 and every positive n; it makes no claim about uppercase V."))),
            DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        Formula V(Formula index) => new Formula.Apply(F.Id("v"), [x, index]);
        Formula Index(FormulaBinaryOperator op) => new Formula.Binary(n, op, D(1));
        var conclusion = new Formula.Relation(new Formula.Power(V(n), D(2)),
            FormulaRelationOperator.GreaterThan,
            new Formula.Binary(V(Index(FormulaBinaryOperator.Subtract)),
                FormulaBinaryOperator.Multiply, V(Index(FormulaBinaryOperator.Add))));
        return Disp(Seq(Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Sp, Le, Sp, n, Sp, Rightarrow, Sp,
            Forall, Sp, x, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            x, Sp, Le, Sp, Minus, Open, new Formula.Fraction(D(1), D(8)), Close,
            Sp, Rightarrow, Sp, conclusion));
    }
}
