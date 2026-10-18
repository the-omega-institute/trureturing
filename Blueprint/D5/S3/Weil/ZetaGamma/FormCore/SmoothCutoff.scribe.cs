using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class SmoothCutoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.",
        H("Actual Gamma form core: SmoothCutoff"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualcutoffeta"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualCutoffEta"),
                H("actualCutoffEta"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: def actualCutoffEta (a ε x : ℝ) : ℝ :=\n  Real.smoothTransition ((x + a) / ε - 1) *\n    Real.smoothTransition ((a - x) / ε - 1)\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffSupport, D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation, D5.S3.Weil.ZetaGamma.FormCore.SmoothCore, D5.S3.Weil.ZetaGamma.FormCore.Corner.actualCutoffEta_contDiff, D5.S3.Weil.ZetaGamma.FormCore.Corner.actualCutoffEta_range, D5.S3.Weil.ZetaGamma.FormCore.Corner.actualCutoffMask, D5.S3.Weil.ZetaGamma.FormCore.Corner.actual_smooth_cutoff_commutator.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualcutoffmask"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualCutoffMask"),
                H("actualCutoffMask"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: def actualCutoffMask (a ε x : ℝ) : ℝ :=\n  if x ∈ Ioo (-a) a then 1 - actualCutoffEta a ε x else 0\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.CutoffSupport, D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation, D5.S3.Weil.ZetaGamma.FormCore.Corner.actualCutoffMask_eventually_zero, D5.S3.Weil.ZetaGamma.FormCore.Corner.actualCutoffMask_measurable, D5.S3.Weil.ZetaGamma.FormCore.Corner.actualCutoffMask_range, D5.S3.Weil.ZetaGamma.FormCore.Corner.actualCutoffMask_tendsto_zero, D5.S3.Weil.ZetaGamma.FormCore.Corner.actual_smooth_cutoff_commutator.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualcutoffeta-contdiff"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualCutoffEta_contDiff"),
                H("actualCutoffEta contDiff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffEta_contDiff (a ε : ℝ) :\n    ContDiff ℝ ∞ (actualCutoffEta a ε)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffSupport, D5.S3.Weil.ZetaGamma.FormCore.SmoothCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualcutoffeta-range"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualCutoffEta_range"),
                H("actualCutoffEta range"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffEta_range (a ε x : ℝ) :\n    0 ≤ actualCutoffEta a ε x ∧ actualCutoffEta a ε x ≤ 1")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.SmoothCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualcutoffmask-measurable"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualCutoffMask_measurable"),
                H("actualCutoffMask measurable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffMask_measurable (a ε : ℝ) :\n    Measurable (actualCutoffMask a ε)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.CutoffSupport.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualcutoffmask-range"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualCutoffMask_range"),
                H("actualCutoffMask range"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffMask_range (a ε x : ℝ) :\n    0 ≤ actualCutoffMask a ε x ∧ actualCutoffMask a ε x ≤ 1")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.CutoffSupport.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualcutoffmask-eventually-zero"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualCutoffMask_eventually_zero"),
                H("actualCutoffMask eventually zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffMask_eventually_zero (a x : ℝ) :\n    ∀ᶠ ε in 𝓝[Ioi (0 : ℝ)] 0, actualCutoffMask a ε x = 0")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffSupport.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualcutoffmask-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualCutoffMask_tendsto_zero"),
                H("actualCutoffMask tendsto zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualCutoffMask_tendsto_zero (a x : ℝ) :\n    Tendsto (fun ε => actualCutoffMask a ε x) (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-cutoffradialgap"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.cutoffRadialGap"),
                H("cutoffRadialGap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: def cutoffRadialGap (b : ℝ → ℝ) (y r : ℝ) : ℝ :=\n  actualDensity r * ((b (y + r) - b y) ^ 2 + (b (y - r) - b y) ^ 2)\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.Corner.actual_smooth_cutoff_commutator, D5.S3.Weil.ZetaGamma.FormCore.Corner.cutoffRadialGap_nonneg.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-cutofffullgap"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.cutoffFullGap"),
                H("cutoffFullGap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: def cutoffFullGap (b : ℝ → ℝ) (y x : ℝ) : ℝ :=\n  actualDensity |x - y| * (b x - b y) ^ 2\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Corner.actual_smooth_cutoff_commutator.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualexteriorpotential"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualExteriorPotential"),
                H("actualExteriorPotential"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: def actualExteriorPotential (a y : ℝ) : ℝ :=\n  (∫ r in Ioi (a - y), actualDensity r) +\n    ∫ r in Ioi (a + y), actualDensity r\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget, D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.Corner.actual_smooth_cutoff_commutator.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualdensity-tail-integrable-for-cutoff"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualDensity_tail_integrable_for_cutoff"),
                H("actualDensity tail integrable for cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualDensity_tail_integrable_for_cutoff {r : ℝ} (hr : 0 < r) :\n    IntegrableOn actualDensity (Ioi r)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-cutoffradialgap-nonneg"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.cutoffRadialGap_nonneg"),
                H("cutoffRadialGap nonneg"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem cutoffRadialGap_nonneg (b : ℝ → ℝ) (y : ℝ) {r : ℝ} (hr : 0 < r) :\n    0 ≤ cutoffRadialGap b y r")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actualdensity-tail-nonneg"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actualDensity_tail_nonneg"),
                H("actualDensity tail nonneg"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualDensity_tail_nonneg {δ : ℝ} (hd : 0 < δ) :\n    0 ≤ ∫ r in Ioi δ, actualDensity r")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.ExteriorBudget, D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcutoff-actual-smooth-cutoff-commutator"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCutoff.actual_smooth_cutoff_commutator"),
                H("actual smooth cutoff commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Eta(a,epsilon,x)=smoothTransition((x+a)/epsilon-1)*smoothTransition((a-x)/epsilon-1); the error mask is 1-eta inside Ioo(-a,a) and zero outside. The global derivative bound of the actual smooth transition supplies the commutator envelope. Its radial and full-line Gamma integrals are bounded by a fixed constant plus twice the actual exterior potential, and tend to zero for each interior y as positive epsilon tends to zero. All mask supplier hypotheses are discharged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_smooth_cutoff_commutator :\n    ∃ C0 : ℝ, 0 ≤ C0 ∧\n      (∀ a ε : ℝ, ContDiff ℝ ∞ (actualCutoffEta a ε)) ∧\n      ∀ a y : ℝ, y ∈ Ioo (-a) a →\n        ((∀ ε : ℝ, 0 < ε →\n            IntegrableOn (cutoffRadialGap (actualCutoffMask a ε) y) (Ioi 0) ∧\n              (∫ r in Ioi 0, cutoffRadialGap (actualCutoffMask a ε) y r) ≤\n                C0 + 2 * actualExteriorPotential a y) ∧\n          Tendsto (fun ε => ∫ r in Ioi 0, cutoffRadialGap (actualCutoffMask a ε) y r)\n            (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0)) ∧\n        ((∀ ε : ℝ, 0 < ε →\n            Integrable (cutoffFullGap (actualCutoffMask a ε) y) ∧\n              (∫ x, cutoffFullGap (actualCutoffMask a ε) y x) ≤\n                C0 + 2 * actualExteriorPotential a y) ∧\n          Tendsto (fun ε => ∫ x, cutoffFullGap (actualCutoffMask a ε) y x)\n            (𝓝[Ioi (0 : ℝ)] 0) (𝓝 0))")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
