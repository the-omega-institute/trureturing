using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class LowCutoffObservationFibresDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every instantaneous datum inside the unit frequency cutoff is a function of the pair alpha and alpha times beta.",
        H("Low Cutoff Observation Fibres"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("low-cutoff-fibres-datum"),
                DeclarationHandle.Create(Prefix + "lowCutoffDatum"),
                H("lowCutoffDatum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete instantaneous datum visible inside the squared-frequency cutoff."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-cutoff-fibres-level-sets"),
                DeclarationHandle.Create(Prefix + "lowCutoffDatum_eq_iff"),
                H("lowCutoffDatum eq iff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fibres of the low-cutoff datum are exactly the level sets of the pair alpha and alpha times beta."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-cutoff-fibres-gap"),
                DeclarationHandle.Create(Prefix + "cutoffGap"),
                H("cutoffGap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A real-valued gap on the low-cutoff datum, built from the visible amplitude slot and the transverse acceleration slot."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-cutoff-fibres-gap-zero"),
                DeclarationHandle.Create(Prefix + "cutoffGap_eq_zero_iff"),
                H("cutoffGap eq zero iff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The gap vanishes exactly on the fibres."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-cutoff-fibres-uniform-claim"),
                DeclarationHandle.Create(Prefix + "UniformlyStableCutoffBetaRecovery"),
                H("UniformlyStableCutoffBetaRecovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The claim that beta is recoverable from the low-cutoff datum with a modulus of continuity uniform over the whole family."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("low-cutoff-fibres-no-uniform-modulus"),
                DeclarationHandle.Create(Prefix + "not_uniformlyStableCutoffBetaRecovery"),
                H("not uniformlyStableCutoffBetaRecovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("No uniform modulus exists: shrinking the visible amplitude makes the gap arbitrarily small while the hidden amplitudes stay a fixed distance apart."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-cutoff-fibres-slab-modulus"),
                DeclarationHandle.Create(Prefix + "cutoff_beta_modulus_on_slab"),
                H("cutoff beta modulus on slab"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the slab where the visible amplitude is at least a, recovery of beta is Lipschitz with constant four over a."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-cutoff-fibres-slab-modulus-attained"),
                DeclarationHandle.Create(Prefix + "cutoff_beta_modulus_on_slab_sharp"),
                H("cutoff beta modulus on slab sharp"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The slab constant four over a is attained, so it cannot be improved."))),
                DescribeRole.Theorem))));
}
