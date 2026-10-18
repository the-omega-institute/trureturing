using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class EvenCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every real a, u with MemLp u 2 on Ioc(-a,a), finite actual-Gamma directional energy of F=PeriodicEnergyTransport.zeroExtension (2*a) (-a) u, and AE evenness F(-x)=F(x), every positive real epsilon admits a canonical bundled WeilTestFunction g with tsupport(g) subset Ioo(-a,a). The whole-line endpoint bounds integral_R |g-F|^2 plus actual directional energy of g-F by ofReal(epsilon); the on-source endpoint replaces only the mass term by integral_Ioc |g-u|^2. After the inward cutoff and mollification, symmetrize H by (H(x)+H(-x))/2. Reflection invariance and graph contraction preserve the error, smoothness and interior support. No pointwise evenness, continuity, endpoint trace or Fourier-L2 premise is imposed on u. The statements include empty and nonpositive windows.",
        H("Actual Gamma form core: EvenCore"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-evencore-actual-ioc-exists-weil-test-core-approximation"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/EvenCore.actual_ioc_exists_weil_test_core_approximation"),
                H("actual ioc exists weil test core approximation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real a, u with MemLp u 2 on Ioc(-a,a), finite actual-Gamma directional energy of F=PeriodicEnergyTransport.zeroExtension (2*a) (-a) u, and AE evenness F(-x)=F(x), every positive real epsilon admits a canonical bundled WeilTestFunction g with tsupport(g) subset Ioo(-a,a). The whole-line endpoint bounds integral_R |g-F|^2 plus actual directional energy of g-F by ofReal(epsilon); the on-source endpoint replaces only the mass term by integral_Ioc |g-u|^2. After the inward cutoff and mollification, symmetrize H by (H(x)+H(-x))/2. Reflection invariance and graph contraction preserve the error, smoothness and interior support. No pointwise evenness, continuity, endpoint trace or Fourier-L2 premise is imposed on u. The statements include empty and nonpositive windows.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_ioc_exists_weil_test_core_approximation\n    (a : ℝ) (u : ℝ → ℂ)\n    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))\n    (henergy : directionalEnergy actualGammaExitMeasure\n      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))\n    (heven : ∀ᵐ x : ℝ ∂volume,\n      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u (-x) =\n        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x)\n    (ε : ℝ) (hε : 0 < ε) :\n    let F := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u\n    ∃ g : D5.S3.Weil.TestFunctions.WeilTestFunction,\n      tsupport (g : ℝ → ℂ) ⊆ Ioo (-a) a ∧\n      coreL2Mass (fun x => g x - F x) +\n        directionalEnergy actualGammaExitMeasure (fun x => g x - F x) <\n          ENNReal.ofReal ε")),
                    Paragraph(Text("Retained result on the delivery surface.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-evencore-actual-ioc-exists-weil-test-core-approximation-on-source"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/EvenCore.actual_ioc_exists_weil_test_core_approximation_on_source"),
                H("actual ioc exists weil test core approximation on source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real a, u with MemLp u 2 on Ioc(-a,a), finite actual-Gamma directional energy of F=PeriodicEnergyTransport.zeroExtension (2*a) (-a) u, and AE evenness F(-x)=F(x), every positive real epsilon admits a canonical bundled WeilTestFunction g with tsupport(g) subset Ioo(-a,a). The whole-line endpoint bounds integral_R |g-F|^2 plus actual directional energy of g-F by ofReal(epsilon); the on-source endpoint replaces only the mass term by integral_Ioc |g-u|^2. After the inward cutoff and mollification, symmetrize H by (H(x)+H(-x))/2. Reflection invariance and graph contraction preserve the error, smoothness and interior support. No pointwise evenness, continuity, endpoint trace or Fourier-L2 premise is imposed on u. The statements include empty and nonpositive windows.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_ioc_exists_weil_test_core_approximation_on_source\n    (a : ℝ) (u : ℝ → ℂ)\n    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))\n    (henergy : directionalEnergy actualGammaExitMeasure\n      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))\n    (heven : ∀ᵐ x : ℝ ∂volume,\n      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u (-x) =\n        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x)\n    (ε : ℝ) (hε : 0 < ε) :\n    ∃ g : D5.S3.Weil.TestFunctions.WeilTestFunction,\n      tsupport (g : ℝ → ℂ) ⊆ Ioo (-a) a ∧\n      (∫⁻ x in Ioc (-a) a, ‖g x - u x‖ₑ ^ 2) +\n        directionalEnergy actualGammaExitMeasure\n          (fun x => g x - D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x) <\n            ENNReal.ofReal ε")),
                    Paragraph(Text("Retained result on the delivery surface.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
