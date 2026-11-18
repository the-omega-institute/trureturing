using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialSlitPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/OriginalHalfBinomialSlitPeriod.";

    private static DocumentBlock Result(string id, string declaration, string title, string text,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Principal Euler continuation of the literal half-binomial-square period.",
        H("The Original Period on the Slit Plane"),
        Blocks(
            Result("slit-domain", "slitDomain", "The period domain",
                "A parameter r belongs to the slit domain when 1 − r belongs to the principal complex slit plane.",
                DescribeRole.Definition),
            Result("double-slit", "doubleSlit", "The complementary period domain",
                "Both r and 1 − r belong to the principal complex slit plane.",
                DescribeRole.Definition),
            Result("slit-period", "slitPeriod", "Euler's principal integral",
                "Integrate the principal complex power (1 − r sin² θ)^(−1/2) on [0, π/2] and multiply by 2/π.",
                DescribeRole.Definition),
            Result("slit-differentiable", "slitPeriod_differentiableAt", "Differentiation under the integral",
                "On the slit domain the kernel stays off the branch cut. Its parameter derivative "
                + "is bounded on a smaller closed parameter disk times the integration interval. "
                + "Dominated differentiation proves complex differentiability."),
            Result("slit-analytic", "slitPeriod_analyticOnNhd", "Holomorphy on the slit domain",
                "The Euler period is holomorphic on a neighborhood of every point of the open slit domain."),
            Result("original-disk", "slitPeriod_eq_period", "Equality with the original series",
                "On the full open unit disk the Euler period equals OriginalHalfBinomialPeriod.period. "
                + "The dominated sine-moment calculation identifies the real values, and holomorphic "
                + "uniqueness extends the equality to complex parameters."),
            Result("slit-positive", "slitPeriod_re_pos", "Positive real part",
                "The principal square root has positive real part off its cut. Its reciprocal "
                + "has the same strict sign, which persists under the normalized integral."),
            Result("slit-nonzero", "slitPeriod_ne_zero", "Nonvanishing of the period",
                "The positive real part excludes zeros everywhere on the slit domain."),
            Result("complementary-ratio", "tau", "The complementary ratio",
                "Multiply the Euler period at 1 − r by i and divide by the Euler period at r.",
                DescribeRole.Definition),
            Result("ratio-positive", "tau_im_pos", "Positive imaginary part of the complementary ratio",
                "Pair the conjugate kernel at r with the kernel at 1 − r. Their product has positive "
                + "real part from the imaginary parts of the square roots and of their squared product. "
                + "Integrating twice and dividing by the squared norm of the period gives the strict sign."),
            Result("pfaff-domain", "pfaff_mem_slitDomain", "Pfaff preserves the slit domain",
                "The complement of r/(r − 1) is the reciprocal of 1 − r and stays off the cut."),
            Describe.Lean(DescribeId.Create("pfaff"), DeclarationHandle.Create(Prefix + "pfaff"),
                H("The Pfaff transformation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/nist2026dlmfpfaff")),
                Blocks(Paragraph(Text(
                    "On the full slit domain the period at r/(r − 1) equals the principal square root of 1 − r "
                    + "times the period at r. This is DLMF 15.8.1 at a = b = 1/2 and c = 1, with the period "
                    + "normalization from DLMF 19.5.1. The Lean proof reflects the real integration variable "
                    + "about π/4 for real r < 1 and extends the identity to the slit domain by analytic uniqueness."))),
                DescribeRole.Theorem),
            Result("slit-wronskian", "slit_wronskian", "The exact complementary Wronskian",
                "On the double slit, r(1 − r) times the sum of P′(r)P(1 − r) and P(r)P′(1 − r) "
                + "equals 1/π. The disk identities also identify the local derivatives, so the existing "
                + "lens Wronskian extends by uniqueness."),
            Result("ratio-derivative", "tau_hasDerivAt", "The quotient derivative",
                "The complex derivative of the complementary ratio is −i/(π r (1 − r) P(r)²) on the double slit."),
            Result("ratio-compact-bound", "exists_pos_le_tau_im", "Uniform positivity on compact subsets",
                "The imaginary part of the complementary ratio has a strictly positive lower bound "
                + "on each compact subset of the double slit."),
            Result("chart-compact-bound", "exists_pos_le_tau_im_charts", "Uniform positivity in the three crossing charts",
                "The continuous images of a compact set of nonreal cross-ratios under 1 − 1/z, z and 1/z "
                + "have a common strictly positive lower bound for the imaginary part of the corresponding ratio."))));
}
