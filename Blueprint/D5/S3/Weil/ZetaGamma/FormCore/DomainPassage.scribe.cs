using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class DomainPassageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At a>0 and original Ioc interval MemLp 2, the finite common-cutoff identities and full boundary limit give equivalence of full zero-extension and periodic energy integrability, with E0=Ep+B0 on that domain. AECover is applied to nonnegative energies to establish the previously unknown integrability. No subtraction of infinite energies or assumed finite comparison energy occurs.",
        H("Actual Gamma form core: DomainPassage"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-domainpassage-density"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DomainPassage.density"),
                H("density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a>0 and original Ioc interval MemLp 2, the finite common-cutoff identities and full boundary limit give equivalence of full zero-extension and periodic energy integrability, with E0=Ep+B0 on that domain. AECover is applied to nonnegative energies to establish the previously unknown integrability. No subtraction of infinite energies or assumed finite comparison energy occurs.")),
                    Paragraph(Text("Exact uncompiled source signature: abbrev density :=\n  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain, D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.cutoffKernel, D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.density_nonneg, D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.periodicEnergyDensity, D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.zeroEnergyDensity.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-domainpassage-intervalmeasure"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DomainPassage.intervalMeasure"),
                H("intervalMeasure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a>0 and original Ioc interval MemLp 2, the finite common-cutoff identities and full boundary limit give equivalence of full zero-extension and periodic energy integrability, with E0=Ep+B0 on that domain. AECover is applied to nonnegative energies to establish the previously unknown integrability. No subtraction of infinite energies or assumed finite comparison energy occurs.")),
                    Paragraph(Text("Exact uncompiled source signature: def intervalMeasure (d t : ℝ) : Measure ℝ :=\n  volume.restrict (Ioc t (t + d))\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.cutoffBoundaryPair, D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.periodicEnergyDensity.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-domainpassage-zeroenergydensity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DomainPassage.zeroEnergyDensity"),
                H("zeroEnergyDensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a>0 and original Ioc interval MemLp 2, the finite common-cutoff identities and full boundary limit give equivalence of full zero-extension and periodic energy integrability, with E0=Ep+B0 on that domain. AECover is applied to nonnegative energies to establish the previously unknown integrability. No subtraction of infinite energies or assumed finite comparison energy occurs.")),
                    Paragraph(Text("Exact uncompiled source signature: def zeroEnergyDensity (d t : ℝ) (u : ℝ → ℂ) (s : ℝ) : ℝ :=\n  density s * ∫ x : ℝ, Complex.normSq\n    (zeroExtension d t u x - zeroExtension d t u (x - s))\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain, D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.actual_centered_gamma_full_domain_equivalence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-domainpassage-periodicenergydensity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DomainPassage.periodicEnergyDensity"),
                H("periodicEnergyDensity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a>0 and original Ioc interval MemLp 2, the finite common-cutoff identities and full boundary limit give equivalence of full zero-extension and periodic energy integrability, with E0=Ep+B0 on that domain. AECover is applied to nonnegative energies to establish the previously unknown integrability. No subtraction of infinite energies or assumed finite comparison energy occurs.")),
                    Paragraph(Text("Exact uncompiled source signature: def periodicEnergyDensity (d t : ℝ) [Fact (0 < d)]\n    (u : ℝ → ℂ) (s : ℝ) : ℝ :=\n  density s * ∫ x : ℝ, Complex.normSq\n    (u x - periodicExtension d t u (x - s)) ∂intervalMeasure d t\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain, D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.actual_centered_gamma_full_domain_equivalence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-domainpassage-cutoffkernel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DomainPassage.cutoffKernel"),
                H("cutoffKernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a>0 and original Ioc interval MemLp 2, the finite common-cutoff identities and full boundary limit give equivalence of full zero-extension and periodic energy integrability, with E0=Ep+B0 on that domain. AECover is applied to nonnegative energies to establish the previously unknown integrability. No subtraction of infinite energies or assumed finite comparison energy occurs.")),
                    Paragraph(Text("Exact uncompiled source signature: def cutoffKernel (ε s : ℝ) : ℝ :=\n  if ε < |s| then density |s| else 0\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.cutoffBoundaryPair.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-domainpassage-cutoffboundarypair"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DomainPassage.cutoffBoundaryPair"),
                H("cutoffBoundaryPair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a>0 and original Ioc interval MemLp 2, the finite common-cutoff identities and full boundary limit give equivalence of full zero-extension and periodic energy integrability, with E0=Ep+B0 on that domain. AECover is applied to nonnegative energies to establish the previously unknown integrability. No subtraction of infinite energies or assumed finite comparison energy occurs.")),
                    Paragraph(Text("Exact uncompiled source signature: def cutoffBoundaryPair (d t ε : ℝ) (u : ℝ → ℂ) : ℝ :=\n  (∫ p : ℝ × ℝ, conj (u p.1) *\n    ((∑' m : ℤ, if m = 0 then 0 else\n      cutoffKernel ε (p.1 - p.2 + m • d)) : ℂ) * u p.2\n    ∂(intervalMeasure d t).prod (intervalMeasure d t)).re\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.actual_centered_gamma_full_domain_equivalence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-domainpassage-density-nonneg"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DomainPassage.density_nonneg"),
                H("density nonneg"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a>0 and original Ioc interval MemLp 2, the finite common-cutoff identities and full boundary limit give equivalence of full zero-extension and periodic energy integrability, with E0=Ep+B0 on that domain. AECover is applied to nonnegative energies to establish the previously unknown integrability. No subtraction of infinite energies or assumed finite comparison energy occurs.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem density_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ density s")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-domainpassage-actual-centered-gamma-full-domain-equivalence"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/DomainPassage.actual_centered_gamma_full_domain_equivalence"),
                H("actual centered gamma full domain equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At a>0 and original Ioc interval MemLp 2, the finite common-cutoff identities and full boundary limit give equivalence of full zero-extension and periodic energy integrability, with E0=Ep+B0 on that domain. AECover is applied to nonnegative energies to establish the previously unknown integrability. No subtraction of infinite energies or assumed finite comparison energy occurs.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_centered_gamma_full_domain_equivalence\n    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)\n    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :\n    letI : Fact (0 < 2 * a) := ⟨by linarith⟩\n    (IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔\n      IntegrableOn (periodicEnergyDensity (2 * a) (-a) u) (Ioi 0)) ∧\n    (IntegrableOn (periodicEnergyDensity (2 * a) (-a) u) (Ioi 0) →\n      (∫ s in Ioi 0, zeroEnergyDensity (2 * a) (-a) u s) =\n        (∫ s in Ioi 0, periodicEnergyDensity (2 * a) (-a) u s) +\n          cutoffBoundaryPair (2 * a) (-a) 0 u)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.FrequencyDomain.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
