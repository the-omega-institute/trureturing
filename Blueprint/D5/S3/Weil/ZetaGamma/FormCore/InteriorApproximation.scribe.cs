using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class InteriorApproximationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original zero extension is exactly PeriodicEnergyTransport.zeroExtension (2*a) (-a) u. Only MemLp u 2 on Ioc(-a,a) and finite actual energy enter the inward approximation. The singleton endpoint difference from the open window is handled AE, and the whole-line mass equals the original Ioc mass. Choosing a measurable representative preserves both mass and actual energy.",
        H("Actual Gamma form core: InteriorApproximation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-interiorapproximation-actual-gamma-interior-cutoff-form-approximation"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/InteriorApproximation.actual_gamma_interior_cutoff_form_approximation"),
                H("actual gamma interior cutoff form approximation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The original zero extension is exactly PeriodicEnergyTransport.zeroExtension (2*a) (-a) u. Only MemLp u 2 on Ioc(-a,a) and finite actual energy enter the inward approximation. The singleton endpoint difference from the open window is handled AE, and the whole-line mass equals the original Ioc mass. Choosing a measurable representative preserves both mass and actual energy.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_gamma_interior_cutoff_form_approximation\n    (a : ℝ) (F : ℝ → ℂ) (hF : Measurable F) (hF₂ : MemLp F 2)\n    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0)\n    (henergy : directionalEnergy actualGammaExitMeasure F < (⊤ : ℝ≥0∞)) :\n    (∀ ε > 0, HasCompactSupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ∧\n      tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ⊆ Ioo (-a) a) ∧\n    Tendsto (fun ε =>\n      (∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2) +\n        directionalEnergy actualGammaExitMeasure\n          (fun x => (actualCutoffEta a ε x : ℂ) * F x - F x))\n      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 (0 : ℝ≥0∞))")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.SmoothCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-interiorapproximation-actual-ioc-exists-measurable-zero-supported-energy-representative"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/InteriorApproximation.actual_ioc_exists_measurable_zero_supported_energy_representative"),
                H("actual ioc exists measurable zero supported energy representative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The original zero extension is exactly PeriodicEnergyTransport.zeroExtension (2*a) (-a) u. Only MemLp u 2 on Ioc(-a,a) and finite actual energy enter the inward approximation. The singleton endpoint difference from the open window is handled AE, and the whole-line mass equals the original Ioc mass. Choosing a measurable representative preserves both mass and actual energy.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_ioc_exists_measurable_zero_supported_energy_representative\n    (a : ℝ) (u : ℝ → ℂ)\n    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :\n    ∃ G : ℝ → ℂ, Measurable G ∧ MemLp G 2 ∧\n      (∀ x ∉ Ioo (-a) a, G x = 0) ∧\n      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u =ᵐ[volume] G ∧\n      ((∫⁻ x : ℝ,\n          ‖D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x‖ₑ ^ 2) =\n        ∫⁻ x : ℝ, ‖G x‖ₑ ^ 2) ∧\n      ((∫⁻ x in Ioc (-a) a, ‖u x‖ₑ ^ 2) = ∫⁻ x : ℝ, ‖G x‖ₑ ^ 2) ∧\n      directionalEnergy actualGammaExitMeasure\n        (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) =\n          directionalEnergy actualGammaExitMeasure G")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.SmoothCore, D5.S3.Weil.ZetaGamma.FormCore.EvenCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
