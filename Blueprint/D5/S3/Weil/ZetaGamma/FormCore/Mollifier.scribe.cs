using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class MollifierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Start from a measurable L2 representative with compact support in Icc(-a+eta,a-eta), eta>0, and finite actual-Gamma energy. Convolve with the actual normalized ContDiffBump approximate identity. Its Fourier multiplier is bounded by one and tends to one; dominated convergence against mass and the actual digamma-weighted spectral measure proves joint mass-plus-energy convergence. Small outer bump radius keeps support strictly within Ioo(-a,a).",
        H("Actual Gamma form core: Mollifier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-mollifier-corel2mass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/Mollifier.coreL2Mass"),
                H("coreL2Mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Start from a measurable L2 representative with compact support in Icc(-a+eta,a-eta), eta>0, and finite actual-Gamma energy. Convolve with the actual normalized ContDiffBump approximate identity. Its Fourier multiplier is bounded by one and tends to one; dominated convergence against mass and the actual digamma-weighted spectral measure proves joint mass-plus-energy convergence. Small outer bump radius keeps support strictly within Ioo(-a,a).")),
                    Paragraph(Text("Exact uncompiled source signature: def coreL2Mass (G : ℝ → ℂ) : ℝ≥0∞ := ∫⁻ x : ℝ, ‖G x‖ₑ ^ 2\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.SmoothCore, D5.S3.Weil.ZetaGamma.FormCore.EvenCore, D5.S3.Weil.ZetaGamma.FormCore.exists_smooth_actual_gamma_approximation_of_inward_support.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-mollifier-exists-smooth-actual-gamma-approximation-of-inward-support"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/Mollifier.exists_smooth_actual_gamma_approximation_of_inward_support"),
                H("exists smooth actual gamma approximation of inward support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Start from a measurable L2 representative with compact support in Icc(-a+eta,a-eta), eta>0, and finite actual-Gamma energy. Convolve with the actual normalized ContDiffBump approximate identity. Its Fourier multiplier is bounded by one and tends to one; dominated convergence against mass and the actual digamma-weighted spectral measure proves joint mass-plus-energy convergence. Small outer bump radius keeps support strictly within Ioo(-a,a).")),
                    Paragraph(Text("Exact uncompiled source signature: theorem exists_smooth_actual_gamma_approximation_of_inward_support\n    (G : ℝ → ℂ) (hG : Measurable G) (hG2 : MemLp G 2 volume)\n    (hGc : HasCompactSupport G)\n    (hGE : directionalEnergy actualGammaExitMeasure G < (⊤ : ℝ≥0∞))\n    (a η : ℝ) (hη : 0 < η) (hGsupport : tsupport G ⊆ Icc (-a + η) (a - η))\n    (ε : ℝ) (hε : 0 < ε) :\n    ∃ H : ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧\n      tsupport H ⊆ Ioo (-a) a ∧\n      coreL2Mass (fun x => H x - G x) +\n        directionalEnergy actualGammaExitMeasure (fun x => H x - G x) <\n          ENNReal.ofReal ε")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.SmoothCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
