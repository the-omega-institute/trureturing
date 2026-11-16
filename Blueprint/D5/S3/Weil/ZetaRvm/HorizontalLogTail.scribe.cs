using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class HorizontalLogTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaRvm/HorizontalLogTail.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponential control and oriented height transport of the actual zeta logarithm tail.",
        H("The principal-log zeta tail"),
        Blocks(
            Paragraph(Text("Put q = pi squared divided by six minus one and C = q/(1-q). "
                + "The shifted Dirichlet series and its square majorant give 0 <= q <= 3/4. "
                + "For real part at least two, each summand gains the factor "
                + "2 to the power (2 minus the real part). Thus zeta stays in the open "
                + "right half-plane, where its actual complex principal logarithm is analytic. "
                + "Every integral below uses Lebesgue volume. This controls Littlewood's right boundary; the central RH sign E <= 0 remains unproved.")),
            Describe.Lean(DescribeId.Create("zeta-right-half-plane"),
                DeclarationHandle.Create(Prefix + "re_zeta_pos_of_two_le_re"),
                H("The zeta image stays in the right half-plane"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex s with real part at least two, "
                    + "Re zeta(s) is positive. The shifted-series bound supplies the strict "
                    + "margin. The principal-log and prime-tail proofs both consume this fact."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("principal-log-decay"),
                DeclarationHandle.Create(Prefix + "norm_log_riemannZeta_le_rpow"),
                H("Uniform exponential decay of the principal logarithm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex s with real part at least two, "
                    + "the norm of Log(zeta(s)) is at most C times 2 to the power "
                    + "(2 minus the real part of s). The power-series remainder bound "
                    + "for log(1+w), applied to w = zeta(s)-1, converts the shifted "
                    + "Dirichlet-series estimate into this bound with the stated C."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-log-tail-integrability"),
                DeclarationHandle.Create(Prefix + "integrableOn_principal_log_riemannZeta_Ioi"),
                H("Integrability of the actual complex tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every R >= 2 and every real height t, "
                    + "sigma mapped to Log(zeta(sigma+it)) is Bochner integrable "
                    + "over the open half-line sigma > R. Continuity supplies "
                    + "measurability, and the exponential bound supplies an integrable majorant."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("real-log-tail-integrability"),
                DeclarationHandle.Create(Prefix + "integrableOn_log_norm_riemannZeta_Ioi"),
                H("Integrability of the real logarithm of the zeta norm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Taking the real part of the complex logarithm "
                    + "gives the actual real log of the zeta norm. Its tail is "
                    + "integrable for the same endpoints and every real height."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("absolute-complex-log-tail"),
                DeclarationHandle.Create(Prefix + "integral_norm_principal_log_riemannZeta_Ioi_le"),
                H("An explicit absolute complex tail estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integral of the norm of the principal logarithm "
                    + "over sigma > R is at most C/log(2) times 2 to the power (2-R), "
                    + "uniformly over every real height. Integrating the exponential "
                    + "majorant gives the displayed coefficient exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("absolute-real-log-tail"),
                DeclarationHandle.Create(Prefix + "integral_abs_log_norm_riemannZeta_Ioi_le"),
                H("The same absolute estimate for the real lognorm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute real part is bounded by the complex "
                    + "norm, so the integral of the absolute real lognorm satisfies "
                    + "the same uniform estimate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("horizontal-log-tail"),
                DeclarationHandle.Create(Prefix + "zetaHorizontalLogTail"),
                H("The improper horizontal lognorm tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("T_R(t) is the actual integral of log(norm(zeta(sigma+it))) "
                    + "over sigma > R. The definition is total; the analytic statements "
                    + "use R >= 2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal-tail-truncation"),
                DeclarationHandle.Create(Prefix + "abs_zetaHorizontalLogTail_sub_intervalIntegral_le"),
                H("A uniform truncation error"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For X >= R >= 2, subtracting the integral from R to X "
                    + "leaves exactly the tail with lower endpoint X. Its absolute value "
                    + "is at most C/log(2) times 2 to the power (2-X), for every real height."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("horizontal-tail-height-transport"),
                DeclarationHandle.Create(Prefix + "zetaHorizontalLogTail_sub_eq_intervalIntegral"),
                H("Oriented transport between arbitrary real heights"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every R >= 2 and all real u and v, T_R(v)-T_R(u) "
                    + "equals the oriented integral from u to v of Im Log(zeta(R+it)). "
                    + "Cauchy's rectangle identity gives the top horizontal real integral "
                    + "minus the bottom one as the left vertical imaginary integral "
                    + "minus the right one. The right edge has absolute value at most "
                    + "C times 2 to the power (2-X) times abs(v-u), which tends to zero "
                    + "as X tends to infinity. Integrability identifies the horizontal "
                    + "limits with the actual improper tails. The oriented formula "
                    + "includes coincident and reversed endpoints. This half-plane "
                    + "identity imposes no condition on zeros in the critical strip."))),
                DescribeRole.Theorem))));
}
