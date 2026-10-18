using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class PeriodicSpectralEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).",
        H("Actual Gamma form core: PeriodicSpectralEnergy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-phasegap"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.phaseGap"),
                H("phaseGap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).")),
                    Paragraph(Text("Exact uncompiled source signature: def phaseGap (n : ℤ) (s : ℝ) : ℝ :=\n  ‖(1 : ℂ) - (@fourier d n) (-(s : AddCircle d))‖ ^ 2\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_spectralWeight, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.extended_window_energy_eq_tsum.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-angularfrequency"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.angularFrequency"),
                H("angularFrequency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).")),
                    Paragraph(Text("Exact uncompiled source signature: def angularFrequency (n : ℤ) : ℝ :=\n  2 * Real.pi * (n : ℝ) / d\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_periodic_energy_eq_tsum, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_spectralWeight.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-physicalcoeff"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.physicalCoeff"),
                H("physicalCoeff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).")),
                    Paragraph(Text("Exact uncompiled source signature: def physicalCoeff (f : AddCircle d → ℂ) (n : ℤ) : ℂ :=\n  (Real.sqrt d : ℂ) * fourierCoeff f n\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_periodic_energy_eq_tsum, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.extended_window_energy_eq_tsum.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-windowgapmass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.windowGapMass"),
                H("windowGapMass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).")),
                    Paragraph(Text("Exact uncompiled source signature: def windowGapMass (t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℝ :=\n  ∫ x : ℝ in Ioc t (t + d),\n    ‖u x - AddCircle.liftIoc d t u ((x - s : ℝ) : AddCircle d)‖ ^ 2\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_periodic_energy_eq_tsum, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.extended_window_energy_eq_tsum.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-extended-window-energy-eq-tsum"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.extended_window_energy_eq_tsum"),
                H("extended window energy eq tsum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).")),
                    Paragraph(Text("Exact uncompiled source signature: theorem extended_window_energy_eq_tsum\n    (k : ℝ → ℝ) (hk : Measurable k) (t : ℝ) (u : ℝ → ℂ)\n    (hu : MemLp u 2 (volume.restrict (Ioc t (t + d)))) :\n    (∫⁻ s : ℝ in Ioi 0,\n      ENNReal.ofReal (k s) * ENNReal.ofReal (windowGapMass (d := d) t u s)) =\n      ∑' n : ℤ,\n        (∫⁻ s : ℝ in Ioi 0,\n          ENNReal.ofReal (k s) * ENNReal.ofReal (phaseGap (d := d) n s)) *\n        ENNReal.ofReal (‖physicalCoeff (AddCircle.liftIoc d t u) n‖ ^ 2)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-gammadensity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.gammaDensity"),
                H("gammaDensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).")),
                    Paragraph(Text("Exact uncompiled source signature: abbrev gammaDensity : ℝ → ℝ :=\n  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_periodic_energy_eq_tsum, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_spectralWeight.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-gammaincrement"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.gammaIncrement"),
                H("gammaIncrement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).")),
                    Paragraph(Text("Exact uncompiled source signature: def gammaIncrement (z : ℝ) : ℝ :=\n  (Complex.digamma ((1 / 4 : ℂ) + Complex.I * ((z / 2 : ℝ) : ℂ))).re -\n    (Complex.digamma (1 / 4)).re\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_periodic_energy_eq_tsum, D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.actual_gamma_spectralWeight.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-actual-gamma-spectralweight"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.actual_gamma_spectralWeight"),
                H("actual gamma spectralWeight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_gamma_spectralWeight (n : ℤ) :\n    (∫⁻ s : ℝ in Ioi 0,\n      ENNReal.ofReal (gammaDensity s) * ENNReal.ofReal (phaseGap (d := d) n s)) =\n      ENNReal.ofReal (gammaIncrement (angularFrequency (d := d) n))")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-periodicspectralenergy-actual-gamma-periodic-energy-eq-tsum"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/PeriodicSpectralEnergy.actual_gamma_periodic_energy_eq_tsum"),
                H("actual gamma periodic energy eq tsum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0 and every original Ioc interval MemLp 2 input, including infinite full energy, the periodic actual-Gamma energy equals the ENNReal coefficient sum. The coefficient is sqrt(d) times Mathlib fourierCoeff with probability Haar measure, so its square has physical Lebesgue normalization. Parseval and nonnegative Tonelli give the phase-gap sum; the canonical owner Levy integral evaluates the weight to Re digamma(1/4+i*omega/2)-Re digamma(1/4).")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_gamma_periodic_energy_eq_tsum\n    (t : ℝ) (u : ℝ → ℂ)\n    (hu : MemLp u 2 (volume.restrict (Ioc t (t + d)))) :\n    (∫⁻ s : ℝ in Ioi 0,\n      ENNReal.ofReal (gammaDensity s) *\n        ENNReal.ofReal (windowGapMass (d := d) t u s)) =\n      ∑' n : ℤ,\n        ENNReal.ofReal (gammaIncrement (angularFrequency (d := d) n)) *\n          ENNReal.ofReal (‖physicalCoeff (AddCircle.liftIoc d t u) n‖ ^ 2)")),
                    Paragraph(Text("Retained result on the delivery surface.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
