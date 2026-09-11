using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class LogOneSubExpDerivativesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithm of one minus a negative exponential is smooth on the positive half-line and has a strictly positive third derivative.",
        H("Logarithmic exponential derivative chain"),
        Blocks(Describe.Lean(
            DescribeId.Create("log-one-sub-exp-derivatives"),
            DeclarationHandle.Create("D5/S3/Analytic/Interpolation/LogOneSubExpDerivatives.log_one_sub_exp_derivatives"),
            H("Three derivatives on the positive half-line"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Here f(t) is log(1-exp(-t)). For t greater than zero the logarithm's argument is positive. Differentiation on this open set gives the three displayed rational expressions. The numerator and denominator in the third expression are strictly positive. Smoothness is asserted on the positive half-line."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("x");
        Formula f = F.Id("f");
        Formula e = Call("exp", x);
        Formula denominator = Seq(Open, e, Minus, D(1), Close);
        Formula first = Call("deriv", f, x);
        Formula second = Call("iteratedDeriv", D(2), f, x);
        Formula third = Call("iteratedDeriv", D(3), f, x);
        Formula chain = Seq(
            first, Sp, Eq, Sp, Frac, Grp(D(1)), Grp(denominator), Sp, Land, Sp,
            second, Sp, Eq, Sp, Minus, Frac, Grp(e), Grp(denominator, Caret, Grp(D(2))), Sp, Land, Sp,
            third, Sp, Eq, Sp, Frac, Grp(e, Open, e, Plus, D(1), Close),
                Grp(denominator, Caret, Grp(D(3))), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, third);
        return Disp(Seq(
            Call("ContDiffOn", Call("Real"), D(3), f, Call("Ioi", D(0))), Sp, Land, Sp,
            Open, Forall, Sp, x, Colon, Sp, Call("Real"), Comma, Sp,
            D(0), Sp, Lt, Sp, x, Sp, Implies, Sp, Open, chain, Close, Close));
    }
}
