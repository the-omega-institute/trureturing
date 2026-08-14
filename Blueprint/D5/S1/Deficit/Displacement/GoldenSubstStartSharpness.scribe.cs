using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Displacement;

internal sealed class GoldenSubstStartSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden substitution-start error has an exact fractional-part form, and both endpoints of its window are sharp.",
        H("Golden Substitution-Start Sharpness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-substitution-start-exact-error"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_eq"),
                H("The substitution-start error has an exact fractional-part form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("v"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("start")), Open, F.Id("v"), Close,
                    Sp, Minus, Sp, Varphi, Sp, F.Id("v"), Sp, Eq, Sp,
                    Varphi, Caret, Grp(Minus, D(1)), Sp, Minus, Sp,
                    OpenBrace, Open, F.Id("v"), Plus, D(1), Close,
                    Varphi, CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Beatty formula writes the substitution start as floor((v+1) phi) minus one. "
                        + "Splitting a real number into its integer floor and fractional part, then using "
                        + "phi minus one equals phi inverse, gives the displayed equality exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-substitution-start-error-window"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_window"),
                H("Every substitution-start error lies in the golden window"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("v"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Minus, Varphi, Caret, Grp(Minus, D(2)), Sp, Leq, Sp,
                    Operatorname, Grp(F.Id("start")), Open, F.Id("v"), Close,
                    Sp, Minus, Sp, Varphi, Sp, F.Id("v"), Sp, Leq, Sp,
                    Varphi, Caret, Grp(Minus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A fractional part is nonnegative and strictly less than one. Applying these two "
                        + "bounds to the exact error formula gives the closed interval from minus phi "
                        + "inverse squared to phi inverse; the identity phi inverse squared plus phi "
                        + "inverse equals one identifies the lower endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-fibonacci-golden-fractional-part"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.fract_fib_mul_goldenRatio"),
                H("Odd Fibonacci indices expose a negative conjugate power"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Odd")), Open, F.Id("k"), Close,
                    Sp, Implies, Sp,
                    OpenBrace, F.Id("Fib"), Open, F.Id("k"), Close,
                    Varphi, CloseBrace, Sp, Eq, Sp,
                    Minus, Psi, Caret, Grp(F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's exact Fibonacci residual says Fib(k+1) minus phi times Fib(k) equals "
                        + "psi to the kth power. For odd k that power lies strictly between minus one "
                        + "and zero, so its negative is already the canonical fractional representative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("even-fibonacci-golden-fractional-part"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.fract_fib_mul_goldenRatio_of_even"),
                H("Even Fibonacci indices expose the complementary conjugate power"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Even")), Open, F.Id("k"), Close,
                    Sp, Implies, Sp,
                    OpenBrace, F.Id("Fib"), Open, F.Id("k"), Close,
                    Varphi, CloseBrace, Sp, Eq, Sp,
                    D(1), Sp, Minus, Sp, Psi, Caret, Grp(F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For even k the conjugate power is positive and at most one. Shifting the integer "
                        + "part of the same Fibonacci residual down by one leaves one minus psi to the "
                        + "kth power in the canonical half-open fractional interval, including k equal to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-substitution-start-upper-endpoint-sharp"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_upper_sharp"),
                H("The upper golden endpoint is sharp"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("epsilon"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("epsilon"), Gt, D(0), Sp, Implies, Sp,
                    Exists, Sp, F.Id("v"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Varphi, Caret, Grp(Minus, D(1)), Sp, Minus, Sp, F.Id("epsilon"),
                    Sp, Lt, Sp,
                    Operatorname, Grp(F.Id("start")), Open, F.Id("v"), Close,
                    Sp, Minus, Sp, Varphi, Sp, F.Id("v")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose v plus one to be Fib(k) with k odd. The exact odd-index formula makes the "
                        + "gap below phi inverse equal to the positive power phi inverse to k. Such powers "
                        + "become smaller than every positive epsilon, proving the upper endpoint sharp."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-substitution-start-lower-endpoint-sharp"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Displacement/GoldenSubstStartSharpness.golden_subst_start_error_lower_sharp"),
                H("The lower golden endpoint is sharp"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("epsilon"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    F.Id("epsilon"), Gt, D(0), Sp, Implies, Sp,
                    Exists, Sp, F.Id("v"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("start")), Open, F.Id("v"), Close,
                    Sp, Minus, Sp, Varphi, Sp, F.Id("v"), Sp, Lt, Sp,
                    Minus, Varphi, Caret, Grp(Minus, D(2)), Sp, Plus, Sp, F.Id("epsilon")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose v plus one to be Fib(k) with k positive and even. The complementary "
                        + "fractional-part formula places the error exactly phi inverse to k above minus "
                        + "phi inverse squared. These powers fall below every positive epsilon, so the "
                        + "lower endpoint is sharp as well. Thus both endpoints of the stated window are proven sharp."))),
                DescribeRole.Theorem))));
}
