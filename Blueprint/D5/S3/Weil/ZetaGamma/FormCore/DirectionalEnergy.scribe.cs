using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class DirectionalEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.",
        H("Actual Gamma form core: DirectionalEnergy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-directionalenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.directionalEnergy"),
                H("directionalEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-exteriorexitpair"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.exteriorExitPair"),
                H("exteriorExitPair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-exteriorpotential"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.exteriorPotential"),
                H("exteriorPotential"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-exterior-mass-le-directionalenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.exterior_mass_le_directionalEnergy"),
                H("exterior mass le directionalEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-complex-norm-add-sq-le"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.complex_norm_add_sq_le"),
                H("complex norm add sq le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-cutoff-outer-majorant-finite"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.cutoff_outer_majorant_finite"),
                H("cutoff outer majorant finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-cutofffirstdensity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.cutoffFirstDensity"),
                H("cutoffFirstDensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-cutofffirstenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.cutoffFirstEnergy"),
                H("cutoffFirstEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-cutofffirstenergy-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.cutoffFirstEnergy_tendsto_zero"),
                H("cutoffFirstEnergy tendsto zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-radialmaskenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.radialMaskEnergy"),
                H("radialMaskEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-radialmaskenergy-measurable"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.radialMaskEnergy_measurable"),
                H("radialMaskEnergy measurable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-directionalenergy-cutoff-le"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.directionalEnergy_cutoff_le"),
                H("directionalEnergy cutoff le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures."))),
                DescribeRole.Theorem))));
}
