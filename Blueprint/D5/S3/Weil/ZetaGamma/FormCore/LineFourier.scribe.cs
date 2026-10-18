using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class LineFourierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.",
        H("Actual Gamma form core: LineFourier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-continuous-raw-fourier"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.continuous_raw_fourier"),
                H("continuous raw fourier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem continuous_raw_fourier {f : ℝ → ℂ} (hf : Integrable f) :\n    Continuous (𝓕 f)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-squared-mass-eq-elpnorm"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.squared_mass_eq_eLpNorm"),
                H("squared mass eq eLpNorm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem squared_mass_eq_eLpNorm (f : ℝ → ℂ)\n    (hf : AEStronglyMeasurable f volume) :\n    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) = eLpNorm f 2 volume ^ 2")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier, D5.S3.Weil.ZetaGamma.FormCore.SmoothCore.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-angularfourier"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angularFourier"),
                H("angularFourier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: def angularFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=\n  𝓕 f (t / (2 * Real.pi))\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier, D5.S3.Weil.ZetaGamma.FormCore.LineFourier.actual_gamma_whole_line_energy_eq_angular_integral, D5.S3.Weil.ZetaGamma.FormCore.LineFourier.angular_extended_plancherel.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-angular-extended-plancherel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.angular_extended_plancherel"),
                H("angular extended plancherel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem angular_extended_plancherel {f : ℝ → ℂ}\n    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :\n    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) =\n      ENNReal.ofReal (1 / (2 * Real.pi)) *\n        ∫⁻ t : ℝ, ‖angularFourier f t‖ₑ ^ 2")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-raw-fourier-sub"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.raw_fourier_sub"),
                H("raw fourier sub"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem raw_fourier_sub {f g : ℝ → ℂ}\n    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :\n    𝓕 (fun x => f x - g x) ξ = 𝓕 f ξ - 𝓕 g ξ")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-linegapmass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.lineGapMass"),
                H("lineGapMass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: def lineGapMass (f : ℝ → ℂ) (s : ℝ) : ℝ :=\n  ∫ x : ℝ, ‖f x - f (x - s)‖ ^ 2\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier, D5.S3.Weil.ZetaGamma.FormCore.LineFourier.actual_gamma_whole_line_energy_eq_angular_integral.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actualdensity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualDensity"),
                H("actualDensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: abbrev actualDensity : ℝ → ℝ :=\n  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier, D5.S3.Weil.ZetaGamma.FormCore.LineFourier.actual_gamma_whole_line_energy_eq_angular_integral, D5.S3.Weil.ZetaGamma.FormCore.LineFourier.actual_line_spectralWeight.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actualincrement"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actualIncrement"),
                H("actualIncrement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: def actualIncrement (z : ℝ) : ℝ :=\n  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * ((z / 2 : ℝ) : ℂ))).re -\n    (Complex.digamma (1 / 4)).re\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier, D5.S3.Weil.ZetaGamma.FormCore.LineFourier.actual_gamma_whole_line_energy_eq_angular_integral, D5.S3.Weil.ZetaGamma.FormCore.LineFourier.actual_line_spectralWeight.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-cyclicgap"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.cyclicGap"),
                H("cyclicGap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: def cyclicGap (ξ s : ℝ) : ℝ :=\n  2 * (1 - Real.cos ((2 * Real.pi * ξ) * s))\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier, D5.S3.Weil.ZetaGamma.FormCore.LineFourier.actual_line_spectralWeight.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actual-line-spectralweight"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_line_spectralWeight"),
                H("actual line spectralWeight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_line_spectralWeight (ξ : ℝ) :\n    (∫⁻ s : ℝ in Ioi 0,\n      ENNReal.ofReal (actualDensity s) * ENNReal.ofReal (cyclicGap ξ s)) =\n      ENNReal.ofReal (actualIncrement (2 * Real.pi * ξ))")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-linefourier-actual-gamma-whole-line-energy-eq-angular-integral"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LineFourier.actual_gamma_whole_line_energy_eq_angular_integral"),
                H("actual gamma whole line energy eq angular integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The raw Fourier transform is identified AE with Mathlib L2 Fourier on integrable L2 functions; Plancherel is normalized to angular frequency with factor 1/(2*pi). For integrable whole-line L2 inputs the actual-Gamma directional energy equals the ENNReal angular-frequency integral with the actual digamma increment, allowing infinity. Fourier-L2 is derived and never added as a compact-core input assumption.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_gamma_whole_line_energy_eq_angular_integral\n    {f : ℝ → ℂ} (hf₁ : Integrable f) (hf₂ : MemLp f 2) :\n    (∫⁻ s : ℝ in Ioi 0,\n      ENNReal.ofReal (actualDensity s) * ENNReal.ofReal (lineGapMass f s)) =\n      ENNReal.ofReal (1 / (2 * Real.pi)) *\n        ∫⁻ z : ℝ, ENNReal.ofReal (actualIncrement z) *\n          ‖angularFourier f z‖ₑ ^ 2")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.Mollifier.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
