using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class CutoffSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis.",
        H("Actual Gamma form core: CutoffSupport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffsupport-actualcutoffeta-mul-eq-sub-mask"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffSupport.actualCutoffEta_mul_eq_sub_mask"),
                H("actualCutoffEta mul eq sub mask"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffEta_mul_eq_sub_mask (a ε : ℝ) (F : ℝ → ℂ)\n    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0) (x : ℝ) :\n    (actualCutoffEta a ε x : ℂ) * F x =\n      F x - (actualCutoffMask a ε x : ℂ) * F x")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffsupport-actualcutoffeta-mul-tsupport-subset-icc"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffSupport.actualCutoffEta_mul_tsupport_subset_Icc"),
                H("actualCutoffEta mul tsupport subset Icc"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffEta_mul_tsupport_subset_Icc {a ε : ℝ} (hε : 0 < ε)\n    (F : ℝ → ℂ) :\n    tsupport (fun x => (actualCutoffEta a ε x : ℂ) * F x) ⊆\n      Icc (-a + ε) (a - ε)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation, D5.S3.Weil.ZetaGamma.FormCore.SmoothCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffsupport-actualcutoffeta-mul-hascompactsupport"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffSupport.actualCutoffEta_mul_hasCompactSupport"),
                H("actualCutoffEta mul hasCompactSupport"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffEta_mul_hasCompactSupport {a ε : ℝ} (hε : 0 < ε)\n    (F : ℝ → ℂ) :\n    HasCompactSupport (fun x => (actualCutoffEta a ε x : ℂ) * F x)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation, D5.S3.Weil.ZetaGamma.FormCore.SmoothCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffsupport-actualcutoffeta-mul-sub-mass-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffSupport.actualCutoffEta_mul_sub_mass_tendsto_zero"),
                H("actualCutoffEta mul sub mass tendsto zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffEta_mul_sub_mass_tendsto_zero (a : ℝ) (F : ℝ → ℂ)\n    (hF : Measurable F)\n    (hmass : (∫⁻ x : ℝ, ‖F x‖ₑ ^ 2) < (⊤ : ℝ≥0∞))\n    (hzero : ∀ x ∉ Ioo (-a) a, F x = 0) :\n    Tendsto (fun ε =>\n        ∫⁻ x : ℝ, ‖(actualCutoffEta a ε x : ℂ) * F x - F x‖ₑ ^ 2)\n      (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
