using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class LowModeReversalWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit two-amplitude incompressible Fourier family has identical low-mode reversals and distinct Leray-projected accelerations.",
        H("Low Mode Reversal Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-mode"),
                DeclarationHandle.Create(Prefix + "Mode"),
                H("Mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integer planar frequencies, embedded in three-space with zero third entry."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-amplitude"),
                DeclarationHandle.Create(Prefix + "Amplitude"),
                H("Amplitude"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three velocity components."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-frequencysquared"),
                DeclarationHandle.Create(Prefix + "frequencySquared"),
                H("frequencySquared"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact integer squared frequency, with no floating comparison."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-frequency"),
                DeclarationHandle.Create(Prefix + "frequency"),
                H("frequency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four modes of the two real cosine waves."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-inputamplitude"),
                DeclarationHandle.Create(Prefix + "inputAmplitude"),
                H("inputAmplitude"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Real cosine amplitudes split equally across each conjugate frequency pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-coefficient"),
                DeclarationHandle.Create(Prefix + "coefficient"),
                H("coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual coefficient, summing every occurrence of an input frequency."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-lowobservation"),
                DeclarationHandle.Create(Prefix + "lowObservation"),
                H("lowObservation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full low-frequency coefficient function."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-advection"),
                DeclarationHandle.Create(Prefix + "advection"),
                H("advection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fourier coefficient of (u dot grad)u, computed by the full input convolution."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-leray"),
                DeclarationHandle.Create(Prefix + "leray"),
                H("leray"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Leray's multiplier I-kk^T/|k|^2, including the identity at k=0. The zero-frequency formula is meaningful because both wave coordinates vanish."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-acceleration"),
                DeclarationHandle.Create(Prefix + "acceleration"),
                H("acceleration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual viscous Fourier multiplier minus the Leray-projected nonlinearity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-input-divergence-free"),
                DeclarationHandle.Create(Prefix + "input_divergence_free"),
                H("input divergence free"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every input coefficient is perpendicular to its actual frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-conjugate-pair-data"),
                DeclarationHandle.Create(Prefix + "conjugate_pair_data"),
                H("conjugate pair data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equal real amplitudes at each opposite-frequency pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-lowobservation-independent"),
                DeclarationHandle.Create(Prefix + "lowObservation_independent"),
                H("lowObservation independent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The low observation forgets beta at every output frequency and component."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-transverse-acceleration"),
                DeclarationHandle.Create(Prefix + "transverse_acceleration"),
                H("transverse acceleration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The output coefficient is derived symbolically for every viscosity and both continuous amplitudes. It is not an assumed finite table entry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-full-partial-reversal-separation"),
                DeclarationHandle.Create(Prefix + "full_partial_reversal_separation"),
                H("full partial reversal separation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full reversal (-1,-1) and visible-only reversal (-1,1) have the same entire low-frequency state and a nonzero low-frequency acceleration gap."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-low-mode-prediction-error-floor"),
                DeclarationHandle.Create(Prefix + "low_mode_prediction_error_floor"),
                H("low mode prediction error floor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every deterministic predictor from the same complete low-mode state has error at least 1/4 on one of the two actual complex acceleration coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-mode-reversal-witness-no-low-mode-acceleration-closure"),
                DeclarationHandle.Create(Prefix + "no_low_mode_acceleration_closure"),
                H("no low mode acceleration closure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("No state-only predictor can recover this actual low acceleration on the whole two-amplitude family, including for every fixed positive viscosity."))),
                DescribeRole.Theorem))));
}
