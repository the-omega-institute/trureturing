using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiLacunaryProfileDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiLacunaryProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete real centered-tent lacunary profile has infinite positive-log "
            + "energy for its actual plus-sign unitary Fourier transform. The physical "
            + "source and sharp sixth-moment construction consume this shared module.",
        H("Explicit lacunary Fourier profile"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-lacunary-counter-profile"),
                DeclarationHandle.Create(Owner + "counterProfile"),
                H("Centered tent and lacunary cosine series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real profile is max(1-4*abs(t-1/2),0) times the cosine "
                        + "series with coefficients 2^(-(n+1)) and frequencies "
                        + "exp(4^(n+1)). Its continuity, support in [1/4,3/4] and "
                        + "value one at the center are proved from the explicit series."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-plus-unitary-fourier"),
                DeclarationHandle.Create(Owner + "unitarySourceFourier"),
                H("Actual positive angular Fourier convention"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The actual transform is (sqrt(2*pi))^(-1) times the mathlib Fourier "
                        + "transform at -xi/(2*pi). Equivalently its genuine L1 integral "
                        + "has kernel exp(i*xi*t) and unitary angular normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-lacunary-positive-log-divergence"),
                DeclarationHandle.Create(Owner + "actual_counterProfile_positive_log_top"),
                H("Actual positive-log Fourier energy is infinite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The genuinely extended nonnegative integral of log-plus(abs(xi)) "
                            + "times the squared norm of the actual transform is infinity. "
                            + "An integrable coefficient-times-tent majorant justifies "
                            + "the series interchange. The tent transform is computed "
                            + "by interval-indicator convolution, including zero frequency.")),
                    Paragraph(Text(
                        "The nonnegative two-channel spectral amplitude has density at "
                            + "least 1/(4096*pi) on pairwise disjoint bands of radius one "
                            + "around the lacunary frequencies. Each band has measure two. "
                            + "The source's Fourier identity is proved, not assumed. "
                            + "The support, center, integral-convention and divergence "
                            + "helpers are exported only for live downstream proofs; "
                            + "this split adds no mathematical claim."))),
                DescribeRole.Theorem))));
}
