using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class SecondMagnusSwapCurvatureDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An alternating Fourier slot kernel modulates finite holonomy into a bounded second-Magnus energy.",
        H("Second-Magnus Swap Curvature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("second-magnus-swap-kernel"),
                DeclarationHandle.Create(Prefix + "secondMagnusSwapKernel"),
                H("Second-Magnus Fourier slot kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The kernel is the determinant obtained by assigning two frequency "
                        + "characters to two fixed time slots and subtracting the swapped "
                        + "assignment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-second-magnus-energy"),
                DeclarationHandle.Create(Prefix + "finiteSecondMagnusEnergy"),
                H("Finite second-Magnus energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each ordered-pair curvature is multiplied by its two-slot Fourier "
                        + "kernel, squared in norm, and summed over the finite carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("stable-residual-second-magnus-energy"),
                DeclarationHandle.Create(Prefix + "stableResidualSecondMagnusEnergy"),
                H("Stable residual second-Magnus energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite second-Magnus construction is specialized to the existing "
                        + "stable residual swap-curvature field."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("swap-frequency"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_swap_frequency"),
                H("Frequency-exchange antisymmetry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exchanging the two frequency labels reverses the orientation and "
                        + "negates the slot kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("swap-time"),
                DeclarationHandle.Create(Prefix + "second_magnus_swap_kernel_swap_time"),
                H("Time-slot antisymmetry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exchanging the two time slots reverses the orientation and negates "
                        + "the slot kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-times"),
                DeclarationHandle.Create(Prefix + "second_magnus_swap_kernel_equal_times"),
                H("Equal-time vanishing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The alternating determinant vanishes when both evaluations use the "
                        + "same time slot."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-frequencies"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_equal_frequencies"),
                H("Equal-frequency vanishing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The alternating determinant vanishes when both channels carry the "
                        + "same frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-norm-bound"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_norm_le_two"),
                H("Uniform kernel norm bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both phase products have unit norm, so their difference has norm at "
                        + "most two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-decomposition"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_center_decomposition"),
                H("Center and relative decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mean time and mean frequency form a common unitary phase. The remaining "
                        + "bracket depends only on the time difference and half the frequency "
                        + "difference."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sine-form"),
                DeclarationHandle.Create(
                    Prefix + "second_magnus_swap_kernel_sine_form"),
                H("Odd sine form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The relative bracket is exactly minus two times the imaginary unit "
                        + "times the sine of half the time-frequency area, multiplied by the "
                        + "common mean phase."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-energy-bound"),
                DeclarationHandle.Create(Prefix + "finite_second_magnus_energy_bound"),
                H("Finite energy domination"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Finite second-Magnus energy is nonnegative and bounded above by four "
                        + "times the underlying finite holonomy energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stable-residual-energy-bound"),
                DeclarationHandle.Create(
                    Prefix + "stable_residual_second_magnus_energy_bound"),
                H("Residual envelope to second-Magnus decay"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Composing finite energy domination with the stable residual holonomy "
                        + "bound makes a vanishing residual envelope sufficient for vanishing "
                        + "finite second-Magnus energy."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/TimeOrderedPrimeMemoryCocycle")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy")),
        ]));
}
