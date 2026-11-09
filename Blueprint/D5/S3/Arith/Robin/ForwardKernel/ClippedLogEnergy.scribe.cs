using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class ClippedLogEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A clipped logarithmic cusp has translation energy bounded linearly in the step, uniformly in its inner and outer radii.",
        H("Translation energy of clipped logarithms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("clipped-log-log-space"),
                DeclarationHandle.Create(Prefix + "clippedLog_log_space"),
                H("Clipping in logarithmic coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<h<k and y nonzero, the clipped logarithm equals min(log(k),max(log(h),log(abs(y))))-log(k)."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For 0<h<k, write ell(y)=log(min(k,max(h,abs(y)))/k). "
                + "The unit logarithmic jump is J(z)=log(abs(z+1))-log(abs(z)). "
                + "All integrals on the real line use Lebesgue measure.")),
            Describe.Lean(
                DescribeId.Create("interval-integrable-log-sq"),
                DeclarationHandle.Create(Prefix + "intervalIntegrable_log_sq"),
                H("Local square integrability of the logarithm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary real endpoints a and b, log(x)^2 is interval integrable from a to b. "
                    + "For positive x, the shared bound log(x)^2<=16*x^(-1/2)+x^2 supplies an integrable "
                    + "majorant on every bounded positive interval; reflection handles negative arguments."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clipped-log-continuous"),
                DeclarationHandle.Create(Prefix + "clippedLog_continuous"),
                H("Continuity of the clipped cusp"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<h<k, ell is continuous on the whole real line. "
                    + "The positive inner radius keeps the argument of the logarithm away from zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-jump-sq-integrable"),
                DeclarationHandle.Create(Prefix + "logJump_sq_integrable"),
                H("Finite energy of the unit logarithmic jump"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function J(z)^2 is integrable over the whole real line. "
                    + "Local square integrability of the logarithm controls the singularities at zero "
                    + "and minus one. For abs(z)>=2, abs(J(z))<=2/abs(z), so its square "
                    + "is dominated by an integrable inverse-square tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("clipped-log-translation-energy"),
                DeclarationHandle.Create(Prefix + "clippedLog_translation_energy"),
                H("Uniform linear translation-energy bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is an absolute constant C>0 such that, for every 0<h<k and u>0, "
                        + "the squared difference (ell(y+u)-ell(y))^2 is integrable over the real line "
                        + "and its integral is at most C*u.")),
                    Paragraph(Text(
                        "Clipping between log(h) and log(k) is a map with Lipschitz constant one. "
                        + "Away from the two points zero and -u, the clipped difference is therefore "
                        + "bounded in absolute value by abs(log(abs(y+u))-log(abs(y))). The substitution "
                        + "y=u*z identifies the square of this latter difference with J(z)^2 and "
                        + "multiplies its integral by u. One can take C=1+integral(J(z)^2). "
                        + "This estimate controls the variance contribution of each translated cusp "
                        + "without a dependence on its depth log(k/h)."))),
                DescribeRole.Theorem))));
}
