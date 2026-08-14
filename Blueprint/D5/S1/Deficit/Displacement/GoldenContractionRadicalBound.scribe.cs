using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Displacement;

internal sealed class GoldenContractionRadicalBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The contraction-face logarithmic error is controlled by the prime radical.",
        H("Golden Contraction Radical Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-contraction-logarithmic-radical-window"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenContractionRadicalBound.log_nS_error_radical_window"),
                H("The hidden-product error lies in a golden radical window"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Minus, Varphi, Caret, Grp(Minus, D(2)), Sp, Cdot, Sp,
                    Log, Grp(Operatorname, Grp(F.Id("rad")), Open, F.Id("n"), Close), Sp,
                    Leq, Sp, Log, Grp(F.Id("nS"), Sp, F.Id("n")), Sp, Minus, Sp,
                    Varphi, Sp, Cdot, Sp, Log, Grp(F.Id("n")), Sp, Leq, Sp,
                    Varphi, Caret, Grp(Minus, D(1)), Sp, Cdot, Sp,
                    Log, Grp(Operatorname, Grp(F.Id("rad")), Open, F.Id("n"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The shifted Zeckendorf Beatty formula places each substituted exponent minus "
                        + "phi times the original exponent between minus phi to the negative second "
                        + "power and phi inverse. Prime logarithms are nonnegative, so summing those "
                        + "pointwise inequalities over the factorization gives the displayed window. "
                        + "The sum of the prime logarithms is exactly the logarithm of the product of "
                        + "the distinct prime factors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-contraction-absolute-radical-bound"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenContractionRadicalBound.abs_lambdaMinus_le_goldenRatio_inv_log_primeRadical"),
                H("The contraction-face length has the documented radical bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("n"), Neq, D(0), Sp, Implies, Sp,
                    Lvert, LambdaLower, Underscore, Grp(Minus), Open, F.Id("n"), Close, Rvert,
                    Sp, Leq, Sp, Varphi, Caret, Grp(Minus, D(1)), Sp, Cdot, Sp,
                    Log, Grp(Operatorname, Grp(F.Id("rad")), Open, F.Id("n"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen contraction-face closed form identifies lambda minus with the middle "
                        + "error term in the first theorem. Since zero is less than phi inverse and phi "
                        + "inverse is at most one, the sharper lower constant phi to the negative second "
                        + "power is no larger than phi inverse. The two sides therefore combine through "
                        + "the absolute-value criterion to give the stated bound."))),
                DescribeRole.Theorem))));
}
