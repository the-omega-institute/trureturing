using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class AugmentedReadoutRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One instantaneous transverse acceleration reading recovers the hidden amplitude on the two-parameter Fourier witness family exactly when the visible amplitude is nonzero.",
        H("Augmented Readout Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("augmented-readout-recovery-low-observation-visible"),
                DeclarationHandle.Create(Prefix + "low_observation_visible"),
                H("low observation visible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The low observation at mode (1,0), component 1, is exactly alpha/2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("augmented-readout-recovery-augmented-readout"),
                DeclarationHandle.Create(Prefix + "augmentedReadout"),
                H("augmentedReadout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete low observation paired with one instantaneous transverse acceleration component."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("augmented-readout-recovery-alpha-recovery"),
                DeclarationHandle.Create(Prefix + "alpha_recovery"),
                H("alpha recovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Twice the real part of the visible observation recovers alpha."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("augmented-readout-recovery-augmented-readout-im"),
                DeclarationHandle.Create(Prefix + "augmented_readout_im"),
                H("augmented readout im"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The imaginary part of the additional reading is -alpha*beta/4."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("augmented-readout-recovery-beta-recovery"),
                DeclarationHandle.Create(Prefix + "beta_recovery"),
                H("beta recovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero alpha, the additional reading recovers beta by explicit division."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("augmented-readout-recovery-beta-recovery-from-readout"),
                DeclarationHandle.Create(Prefix + "beta_recovery_from_readout"),
                H("beta recovery from readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero alpha, both readings alone explicitly reconstruct beta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("augmented-readout-recovery-augmented-readout-zero"),
                DeclarationHandle.Create(Prefix + "augmented_readout_zero"),
                H("augmented readout zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At alpha = 0, every beta gives the same low observation and zero additional reading."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("augmented-readout-recovery-augmented-readout-eq-iff"),
                DeclarationHandle.Create(Prefix + "augmentedReadout_eq_iff"),
                H("augmentedReadout eq iff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two augmented readouts agree exactly when alpha agrees and either alpha is zero or beta agrees."))),
                DescribeRole.Theorem))));
}
