using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class SourceJensenIntegralExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent source Jensen polynomials differ by one exact integration constant.",
        H("Source Jensen Integral Extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-jensen-integral-extension"),
            DeclarationHandle.Create(
                "D5/S3/Zeros/Jensen/SourceJensenIntegralExtension.source_jensen_integral_extension"),
            H("The primitive and its constant"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every natural d at least two, P is the real finite source polynomial "
                    + "with coefficients (d)_k a_k/d^k, where a_k is the frozen "
                    + "sourceThetaCoefficient k. Q is Polynomial.reflect d applied to P(-X). "
                    + "The theorem identifies its complexification with the reflection of the "
                    + "actual sourceJensenPolynomial, so Q is defined at zero as a polynomial.")),
                Paragraph(Math(Definitions())),
                Paragraph(Text(
                    "Every x and every replacement constant b in the formulas is real. "
                    + "The integral is oriented from zero to x; negative x and zero are included. "
                    + "Write Q_b = Q + b - beta. Its derivative is unchanged, its value is R(x)+b, "
                    + "and its roots satisfy R(x)=-b. The two symbolic constants -R(x) and "
                    + "1-R(x) respectively include and exclude the chosen x from the real zero set. "
                    + "This concerns the family obtained by replacing the constant; the actual "
                    + "theta constant remains fixed. No assertion of computational ease or of "
                    + "a real-rooted theta tower follows.")),
                Paragraph(Text(
                    "The proof binds the frozen Jensen degree-lowering identity through "
                    + "Polynomial.coeff_reflect and applies Mathlib's fundamental theorem of "
                    + "calculus. The remaining equalities are coefficient, field, and ring "
                    + "normalization; there is no finite enumeration or new analytic estimate."))),
            DescribeRole.Theorem))));

    private static Formula Dd => F.Id("d");
    private static Formula Xx => F.Id("x");
    private static Formula Bb => F.Id("b");
    private static Formula Sub(Formula f, Formula n) => Seq(f, Underscore, Grp(n));
    private static Formula Pow(Formula f, Formula n) => Seq(f, Caret, Grp(n));
    private static Formula Call(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Q => Sub(F.Id("q"), Dd);
    private static Formula R => Sub(F.Id("R"), Dd);
    private static Formula A => Sub(Alpha, Dd);
    private static Formula B => Sub(Beta, Dd);
    private static Formula Qb(Formula b) => Sub(F.Id("q"), Seq(Dd, Comma, b));
    private static Formula Integrand(Formula x) => Seq(Dd, Pow(A, Seq(Dd, Minus, D(1))),
        Call(Sub(F.Id("q"), Seq(Dd, Minus, D(1))), Div(x, A)));

    private static Formula Definitions() => Disp(Seq(
        A, Eq, Div(Seq(Dd, Minus, D(1)), Dd), Comma, Quad, Sp,
        B, Eq, Pow(Seq(Open, Minus, D(1), Close), Dd),
        Div(Seq(Dd, Bang), Pow(Dd, Dd)), Sub(F.Id("a"), Dd), Comma, Quad, Sp,
        Call(R, Xx), Eq, Int, Underscore, Grp(D(0)), Caret, Grp(Xx),
        Integrand(F.Id("u")), Thin, Sp, F.Id("d"), F.Id("u")));

    private static Formula Statement() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, Dd, Ge, D(2), Comma, Quad, Sp,
        Sub(Grp(Q), MathbbC()), Eq, Sub(Operator(F.Id("reflect")), Dd),
        Open, Call(Sub(F.Id("P"), Dd), Seq(Minus, F.Id("X"))), Close,
        Comma, Quad, Sp, Forall, Sp, Xx, InMacro, MathbbR(), Comma,
        Call(Seq(Q, Apos), Xx), Eq, Integrand(Xx), Comma, RowBreak,
        Call(Q, D(0)), Eq, B, Comma, Quad, Sp, Forall, Sp, Xx, InMacro, MathbbR(), Comma,
        Call(Q, Xx), Eq, Call(R, Xx), Plus, B, Comma, RowBreak,
        Forall, Sp, Bb, Comma, Xx, InMacro, MathbbR(), Comma,
        Qb(Bb), Eq, Q, Plus, Bb, Minus, B, Comma, Quad, Sp,
        Seq(Qb(Bb), Apos), Eq, Seq(Q, Apos), Comma, Quad, Sp,
        Call(Qb(Bb), Xx), Eq, Call(R, Xx), Plus, Bb, Comma, RowBreak,
        Open, Call(Qb(Bb), Xx), Eq, D(0), Iff, Sp, Call(R, Xx), Eq, Minus, Bb, Close,
        Comma, Quad, Sp, Forall, Sp, Xx, InMacro, MathbbR(), Comma,
        Exists, Sp, Sub(Bb, D(0)), Comma, Sub(Bb, D(1)), InMacro, MathbbR(), Comma,
        Call(Qb(Sub(Bb, D(0))), Xx), Eq, D(0), Land, Sp,
        Call(Qb(Sub(Bb, D(1))), Xx), Neq, D(0),
        End, Grp(F.Id("gathered"))));

    private static Formula MathbbR() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula MathbbC() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Operator(Formula name) => Seq(Operatorname, Grp(name));
}
