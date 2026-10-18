using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class SmoothCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For arbitrary real a, original Ioc MemLp 2 and finite actual-Gamma zero-extension energy, choose an inward cutoff and then a small bump convolution. The epsilon/8 diagonal budget, graph-size addition bound and AE congruence give smooth compact approximation with the exact sum of physical squared mass error and actual energy error less than ofReal(epsilon). The on-source version uses the original Ioc mass integral. No evenness is needed in this intermediate result.",
        H("Actual Gamma form core: SmoothCore"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-coregraphsize"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.coreGraphSize"),
                H("coreGraphSize"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary real a, original Ioc MemLp 2 and finite actual-Gamma zero-extension energy, choose an inward cutoff and then a small bump convolution. The epsilon/8 diagonal budget, graph-size addition bound and AE congruence give smooth compact approximation with the exact sum of physical squared mass error and actual energy error less than ofReal(epsilon). The on-source version uses the original Ioc mass integral. No evenness is needed in this intermediate result.")),
                    Paragraph(Text("Exact uncompiled source signature: def coreGraphSize (nu : Measure ℝ) (F : ℝ → ℂ) : ℝ≥0∞ :=\n  coreL2Mass F + directionalEnergy nu F\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.EvenCore, D5.S3.Weil.ZetaGamma.FormCore.coreGraphSize_add_le, D5.S3.Weil.ZetaGamma.FormCore.coreGraphSize_congr_ae.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-coregraphsize-add-le"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.coreGraphSize_add_le"),
                H("coreGraphSize add le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary real a, original Ioc MemLp 2 and finite actual-Gamma zero-extension energy, choose an inward cutoff and then a small bump convolution. The epsilon/8 diagonal budget, graph-size addition bound and AE congruence give smooth compact approximation with the exact sum of physical squared mass error and actual energy error less than ofReal(epsilon). The on-source version uses the original Ioc mass integral. No evenness is needed in this intermediate result.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem coreGraphSize_add_le\n    (nu : Measure ℝ) (F G : ℝ → ℂ) (hF : Measurable F) (hG : Measurable G) :\n    coreGraphSize nu (fun x => F x + G x) ≤\n      2 * coreGraphSize nu F + 2 * coreGraphSize nu G")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.EvenCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-coregraphsize-congr-ae"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.coreGraphSize_congr_ae"),
                H("coreGraphSize congr ae"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary real a, original Ioc MemLp 2 and finite actual-Gamma zero-extension energy, choose an inward cutoff and then a small bump convolution. The epsilon/8 diagonal budget, graph-size addition bound and AE congruence give smooth compact approximation with the exact sum of physical squared mass error and actual energy error less than ofReal(epsilon). The on-source version uses the original Ioc mass integral. No evenness is needed in this intermediate result.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem coreGraphSize_congr_ae\n    (nu : Measure ℝ) {F G : ℝ → ℂ} (hFG : F =ᵐ[volume] G) :\n    coreGraphSize nu F = coreGraphSize nu G")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.EvenCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-actual-ioc-exists-smooth-compact-core-approximation"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.actual_ioc_exists_smooth_compact_core_approximation"),
                H("actual ioc exists smooth compact core approximation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary real a, original Ioc MemLp 2 and finite actual-Gamma zero-extension energy, choose an inward cutoff and then a small bump convolution. The epsilon/8 diagonal budget, graph-size addition bound and AE congruence give smooth compact approximation with the exact sum of physical squared mass error and actual energy error less than ofReal(epsilon). The on-source version uses the original Ioc mass integral. No evenness is needed in this intermediate result.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_ioc_exists_smooth_compact_core_approximation\n    (a : ℝ) (u : ℝ → ℂ)\n    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))\n    (henergy : directionalEnergy actualGammaExitMeasure\n      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))\n    (ε : ℝ) (hε : 0 < ε) :\n    let F := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u\n    ∃ H : ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧\n      tsupport H ⊆ Ioo (-a) a ∧\n      coreL2Mass (fun x => H x - F x) +\n        directionalEnergy actualGammaExitMeasure (fun x => H x - F x) <\n          ENNReal.ofReal ε")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.EvenCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-corel2mass-error-eq-original-ioc"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.coreL2Mass_error_eq_original_ioc"),
                H("coreL2Mass error eq original ioc"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary real a, original Ioc MemLp 2 and finite actual-Gamma zero-extension energy, choose an inward cutoff and then a small bump convolution. The epsilon/8 diagonal budget, graph-size addition bound and AE congruence give smooth compact approximation with the exact sum of physical squared mass error and actual energy error less than ofReal(epsilon). The on-source version uses the original Ioc mass integral. No evenness is needed in this intermediate result.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem coreL2Mass_error_eq_original_ioc\n    (a : ℝ) (u H : ℝ → ℂ) (hHsupport : tsupport H ⊆ Ioo (-a) a) :\n    coreL2Mass (fun x => H x -\n      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x) =\n        ∫⁻ x in Ioc (-a) a, ‖H x - u x‖ₑ ^ 2")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.EvenCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
