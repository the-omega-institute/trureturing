using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenSecondMagnusSamplingDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenSecondMagnusSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden Mellin sample times make second-Magnus curvature descend through whole golden shell shifts.",
        H("Golden Second-Magnus Sampling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-sample-time"),
                DeclarationHandle.Create(Prefix + "goldenSampleTime"),
                H("Golden Mellin sample time"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An integral golden Fourier mode is sent to its vertical Mellin time "
                        + "by multiplying it by the fundamental golden angular frequency."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-scale-circle-point"),
                DeclarationHandle.Create(Prefix + "goldenScaleCirclePoint"),
                H("Visible golden scale-circle point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unwrapped logarithmic golden coordinate is projected to the unit "
                        + "additive circle."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-scale-fourier-phase"),
                DeclarationHandle.Create(Prefix + "goldenScaleFourierPhase"),
                H("Golden scale Fourier character"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral mode character evaluates the visible golden scale "
                        + "coordinate as a unit complex phase."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("circle-point-mul"),
                DeclarationHandle.Create(Prefix + "golden_scale_circle_point_mul"),
                H("Positive multiplication becomes circle addition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication of positive scales adds their unwrapped logarithmic "
                        + "coordinates and therefore adds their visible circle points."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("circle-point-shell"),
                DeclarationHandle.Create(
                    Prefix + "golden_scale_circle_point_phi_even_pow_mul"),
                H("Whole golden shells have one visible circle point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplication by any natural power of phi squared changes the "
                        + "unwrapped coordinate by an integer and is invisible on the unit "
                        + "additive circle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-log-frequency"),
                DeclarationHandle.Create(
                    Prefix + "golden_scale_fourier_phase_eq_log_frequency"),
                H("Golden circle phase equals sampled log-frequency phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The golden circle character is exactly the existing Fourier character "
                        + "of log scale evaluated at the corresponding golden Mellin sample "
                        + "time."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-norm"),
                DeclarationHandle.Create(Prefix + "golden_scale_fourier_phase_norm"),
                H("Golden scale characters have unit norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sampled phase lies on the complex unit circle for every real "
                        + "scale and integral mode."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-mul"),
                DeclarationHandle.Create(Prefix + "golden_scale_fourier_phase_mul"),
                H("Golden scale characters are multiplicative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At one integral mode, the phase of a positive product is the product "
                        + "of the two phases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("phase-shell"),
                DeclarationHandle.Create(
                    Prefix + "golden_scale_fourier_phase_phi_even_pow_mul"),
                H("Integral modes ignore whole golden shell shifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every natural whole-shell shift contributes an integral multiple of a "
                        + "full circle turn, so the complex phase is unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-sampling"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_kernel_at_golden_samples"),
                H("Golden sampling realizes the second-Magnus alternant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At two golden Mellin sample times, the existing second-Magnus kernel "
                        + "is the alternating determinant of four golden scale character "
                        + "values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-shell-invariance"),
                DeclarationHandle.Create(
                    Prefix + "golden_second_magnus_shell_orbit_invariance"),
                H("The sampled kernel descends through shell orbits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Independent whole-shell shifts of the two positive scale inputs leave "
                        + "the sampled second-Magnus kernel unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("energy-shell-invariance"),
                DeclarationHandle.Create(
                    Prefix + "finite_second_magnus_energy_golden_shell_invariant"),
                H("Finite sampled energy descends through channelwise shell orbits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying an independent natural whole-shell shift to every positive "
                        + "scale channel preserves the complete finite second-Magnus "
                        + "energy."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
        ]));
}
