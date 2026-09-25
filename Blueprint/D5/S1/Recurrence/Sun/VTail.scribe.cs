using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Sun;

internal sealed class VTailDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Sun =
        LibraryNoteRef.Create("D5/L/Recurrence/sun2026generalizations");
    private static readonly LibraryNoteRef Krasikov =
        LibraryNoteRef.Create("D5/L/Recurrence/krasikov2011turan");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive radical normalization transports the weighted recurrence bound to a strict lowercase-v tail.",
        H("Strict Turan Tail for v"),
        Blocks(Describe.Lean(
            DescribeId.Create("sun-v-tail-strict"),
            DeclarationHandle.Create("D5/S1/Recurrence/Sun/VTail.v_tail_strict"),
            H("Strictness beyond the v tail threshold"), StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(Sun, Krasikov),
            Blocks(Paragraph(Text("Write R(j)=(-1)^j v(-t,j), "
                + "a(j)=j^3/sqrt(4j^2-1) for j>0, b(j)=j(j+1), "
                + "and q(j)=sqrt(2j+1)R(j). The positive factor d(j)=1/sqrt(2j+1) "
                + "gives R(j)=d(j)q(j). The proof checks both initials and the exact "
                + "recurrence by two-step uniqueness; it does not assume that the source "
                + "sequence has the supplier's normalization. Positivity of the radicals "
                + "and monotonicity of b are proved. Strict increase of a follows by "
                + "clearing positive denominators: at j=k+1 the numerator is "
                + "16k^7+168k^6+746k^5+1815k^4+2604k^3+2187k^2+982k+177, "
                + "positive for k at least zero. The direct supplier call yields a "
                + "weighted nonnegative determinant on the closed threshold "
                + "t at least n(n+1)-2n^3/sqrt(4n^2-1). Exact positive scaling "
                + "transports it to R, with neighbor weight "
                + "(n+1)^3(2n-1)/(n^3(2n+1))>1. The recurrence excludes adjacent "
                + "zeros, and the sign split of the neighbor product makes the "
                + "unweighted determinant strict. VStrict consumes this tail."))),
            DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var t = F.Id("t");
        var nr = Seq(Open, n, Colon, Sp, Mathbb, Grp(F.Id("R")), Close);
        Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
        Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
        Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
        Formula Pow(Formula a, byte e) => new Formula.Power(a, D(e));
        Formula R(Formula index) => Mul(
            new Formula.Power(Seq(Open, Minus, D(1), Close), index),
            new Formula.Apply(F.Id("v"), [Seq(Minus, t), index]));
        var threshold = Sub(Mul(nr, Add(nr, D(1))),
            new Formula.Fraction(Mul(D(2), Pow(nr, 3)),
                Seq(Sqrt, Grp(Sub(Mul(D(4), Pow(nr, 2)), D(1))))));
        var determinant = Sub(Pow(R(n), 2), Mul(R(Sub(n, D(1))), R(Add(n, D(1)))));
        return Disp(Seq(Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Sp, Le, Sp, n, Sp, Rightarrow, Sp,
            Forall, Sp, t, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            new Formula.Relation(threshold, FormulaRelationOperator.LessThanOrEqual, t),
            Sp, Rightarrow, Sp,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, determinant)));
    }
}
