using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class CutoffConvergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual smooth-mask commutator limit and the exterior budget dominate the outer integral, giving cutoff error energy tending to zero for measurable whole-line L2 inputs supported in the open window with finite actual energy. AE congruence then selects a measurable exactly zero-supported representative without adding pointwise regularity to the original source input.",
        H("Actual Gamma form core: CutoffConvergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffconvergence-actual-gamma-cutoff-error-energy-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffConvergence.actual_gamma_cutoff_error_energy_tendsto_zero"),
                H("actual gamma cutoff error energy tendsto zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The actual smooth-mask commutator limit and the exterior budget dominate the outer integral, giving cutoff error energy tending to zero for measurable whole-line L2 inputs supported in the open window with finite actual energy. AE congruence then selects a measurable exactly zero-supported representative without adding pointwise regularity to the original source input.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_gamma_cutoff_error_energy_tendsto_zero\n    (a : ℝ) (F : ℝ → ℂ) (hF : Measurable F) (hF₂ : MemLp F 2)\n    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)\n    (henergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :\n    Tendsto (fun ε => directionalEnergy actualGammaExitMeasure\n      (fun x => (actualCutoffMask a ε x : ℂ) * F x))\n      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞))")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffconvergence-directionalenergy-congr-ae"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffConvergence.directionalEnergy_congr_ae"),
                H("directionalEnergy congr ae"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The actual smooth-mask commutator limit and the exterior budget dominate the outer integral, giving cutoff error energy tending to zero for measurable whole-line L2 inputs supported in the open window with finite actual energy. AE congruence then selects a measurable exactly zero-supported representative without adding pointwise regularity to the original source input.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem directionalEnergy_congr_ae (nu : Measure ℝ)\n    {F G : ℝ → ℂ} (h : F =ᵐ[volume] G) :\n    directionalEnergy nu F = directionalEnergy nu G")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation, D5.S3.Weil.ZetaGamma.FormCore.SmoothCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffconvergence-exists-measurable-zero-supported-energy-representative"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffConvergence.exists_measurable_zero_supported_energy_representative"),
                H("exists measurable zero supported energy representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The actual smooth-mask commutator limit and the exterior budget dominate the outer integral, giving cutoff error energy tending to zero for measurable whole-line L2 inputs supported in the open window with finite actual energy. AE congruence then selects a measurable exactly zero-supported representative without adding pointwise regularity to the original source input.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem exists_measurable_zero_supported_energy_representative\n    (nu : Measure ℝ) (Omega : Set ℝ) (hOmega : MeasurableSet Omega)\n    (F : ℝ → ℂ) (hF : AEMeasurable F)\n    (hzero : ∀ᵐ x : ℝ, x ∉ Omega → F x = 0) :\n    ∃ G : ℝ → ℂ, Measurable G ∧ (∀ x ∉ Omega, G x = 0) ∧\n      F =ᵐ[volume] G ∧\n      (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) = (∫⁻ x : ℝ, ‖G x‖ₑ ^ 2) ∧\n      directionalEnergy nu F = directionalEnergy nu G")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
