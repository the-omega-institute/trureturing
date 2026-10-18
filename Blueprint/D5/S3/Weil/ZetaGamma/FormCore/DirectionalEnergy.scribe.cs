using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
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
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: def directionalEnergy (nu : Measure ℝ) (F : ℝ → ℂ) : ℝ≥0∞ :=\n  ∫⁻ s : ℝ, ∫⁻ x : ℝ, ‖F x - F (x - s)‖ₑ ^ 2 ∂volume ∂nu\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget, D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation, D5.S3.Weil.ZetaGamma.FormCore.Mollifier, D5.S3.Weil.ZetaGamma.FormCore.SmoothCore, D5.S3.Weil.ZetaGamma.FormCore.EvenCore, D5.S3.Weil.ZetaGamma.FormCore.cutoffFirstEnergy_tendsto_zero, D5.S3.Weil.ZetaGamma.FormCore.cutoff_outer_majorant_finite, D5.S3.Weil.ZetaGamma.FormCore.directionalEnergy_cutoff_le, D5.S3.Weil.ZetaGamma.FormCore.exterior_mass_le_directionalEnergy.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-exteriorexitpair"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.exteriorExitPair"),
                H("exteriorExitPair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: def exteriorExitPair (Omega : Set ℝ) (x s : ℝ) : ℝ≥0∞ :=\n  (if x - s ∈ Omega then 0 else 1) +\n    (if x + s ∈ Omega then 0 else 1)\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget, D5.S3.Weil.ZetaGamma.FormCore.exteriorPotential.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-exteriorpotential"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.exteriorPotential"),
                H("exteriorPotential"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: def exteriorPotential (nu : Measure ℝ) (Omega : Set ℝ) (x : ℝ) : ℝ≥0∞ :=\n  ∫⁻ s : ℝ, exteriorExitPair Omega x s ∂nu\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget, D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.cutoff_outer_majorant_finite, D5.S3.Weil.ZetaGamma.FormCore.exterior_mass_le_directionalEnergy.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-exterior-mass-le-directionalenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.exterior_mass_le_directionalEnergy"),
                H("exterior mass le directionalEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem exterior_mass_le_directionalEnergy\n    (nu : Measure ℝ) [SFinite nu] (Omega : Set ℝ)\n    (hOmega : MeasurableSet Omega) (F : ℝ → ℂ) (hF : Measurable F)\n    (hzero : ∀ x ∉ Omega, F x = 0) :\n    (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2 * exteriorPotential nu Omega x) ≤\n      directionalEnergy nu F")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-complex-norm-add-sq-le"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.complex_norm_add_sq_le"),
                H("complex norm add sq le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem complex_norm_add_sq_le (z w : ℂ) :\n    ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.SmoothCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-cutoff-outer-majorant-finite"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.cutoff_outer_majorant_finite"),
                H("cutoff outer majorant finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem cutoff_outer_majorant_finite\n    (nu : Measure ℝ) [SFinite nu] (Omega : Set ℝ)\n    (hOmega : MeasurableSet Omega) (F : ℝ → ℂ) (hF : Measurable F)\n    (hzero : ∀ x ∉ Omega, F x = 0)\n    (hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞))\n    (henergy : directionalEnergy nu F < (⊤ : ℝ≥0∞)) (C : ℝ) :\n    (∫⁻ x : ℝ, ENNReal.ofReal C * ‖F x‖ₑ ^ 2 +\n      2 * (‖F x‖ₑ ^ 2 * exteriorPotential nu Omega x)) < (⊤ : ℝ≥0∞)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-cutofffirstdensity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.cutoffFirstDensity"),
                H("cutoffFirstDensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: def cutoffFirstDensity (b : ℝ → ℝ) (F : ℝ → ℂ)\n    (p : ℝ × ℝ) : ℝ≥0∞ :=\n  ENNReal.ofReal ((b p.2 ^ 2 + b (p.2 - p.1) ^ 2) *\n    ‖F p.2 - F (p.2 - p.1)‖ ^ 2)\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.cutoffFirstEnergy.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-cutofffirstenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.cutoffFirstEnergy"),
                H("cutoffFirstEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: def cutoffFirstEnergy (nu : Measure ℝ) (b : ℝ → ℝ)\n    (F : ℝ → ℂ) : ℝ≥0∞ :=\n  ∫⁻ p : ℝ × ℝ, cutoffFirstDensity b F p ∂nu.prod volume\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.cutoffFirstEnergy_tendsto_zero, D5.S3.Weil.ZetaGamma.FormCore.directionalEnergy_cutoff_le.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-cutofffirstenergy-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.cutoffFirstEnergy_tendsto_zero"),
                H("cutoffFirstEnergy tendsto zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem cutoffFirstEnergy_tendsto_zero\n    (nu : Measure ℝ) [SFinite nu] (F : ℝ → ℂ) (hF : Measurable F)\n    (henergy : directionalEnergy nu F < (⊤ : ℝ≥0∞)) (b : ℝ → ℝ → ℝ)\n    (hb : ∀ ε, Measurable (b ε))\n    (hbound : ∀ ε > 0, ∀ x, 0 ≤ b ε x ∧ b ε x ≤ 1)\n    (hzero : ∀ x, Tendsto (fun ε => b ε x) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)) :\n    Tendsto (fun ε => cutoffFirstEnergy nu (b ε) F)\n      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-radialmaskenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.radialMaskEnergy"),
                H("radialMaskEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: def radialMaskEnergy (nu : Measure ℝ) (b : ℝ → ℝ) (y : ℝ) : ℝ≥0∞ :=\n  ∫⁻ s : ℝ, ENNReal.ofReal\n    ((b (y + s) - b y) ^ 2 + (b (y - s) - b y) ^ 2) ∂nu\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.directionalEnergy_cutoff_le, D5.S3.Weil.ZetaGamma.FormCore.radialMaskEnergy_measurable.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-radialmaskenergy-measurable"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.radialMaskEnergy_measurable"),
                H("radialMaskEnergy measurable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem radialMaskEnergy_measurable\n    (nu : Measure ℝ) [SFinite nu] (b : ℝ → ℝ) (hb : Measurable b) :\n    Measurable (radialMaskEnergy nu b)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-directionalenergy-directionalenergy-cutoff-le"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DirectionalEnergy.directionalEnergy_cutoff_le"),
                H("directionalEnergy cutoff le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Directional energy is the ENNReal integral of squared complex displacement over real Lebesgue x and a jump measure nu. Zero support outside an explicitly measurable window bounds the exit-potential mass by this energy. The cutoff product estimate separates the first displacement term and the radial mask commutator. All finiteness and measurability hypotheses are retained exactly in the attached source signatures.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem directionalEnergy_cutoff_le\n    (nu : Measure ℝ) [SFinite nu] (b : ℝ → ℝ) (hb : Measurable b)\n    (F : ℝ → ℂ) (hF : Measurable F) :\n    directionalEnergy nu (fun x => (b x : ℂ) * F x) ≤\n      cutoffFirstEnergy nu b F +\n        ∫⁻ y : ℝ, ‖F y‖ₑ ^ 2 * radialMaskEnergy nu b y")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
