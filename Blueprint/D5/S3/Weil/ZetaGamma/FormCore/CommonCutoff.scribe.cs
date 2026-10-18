using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class CommonCutoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged.",
        H("Actual Gamma form core: CommonCutoff"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-density"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.density"),
                H("density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged.")),
                    Paragraph(Text("Exact uncompiled source signature: abbrev density :=\n  D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.archimedeanJumpDensity\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.actual_common_cutoff_integrable_and_identity, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.actual_density_tail_integrable, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.cutoffKernel, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.periodicCutoffEnergy, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.zeroCutoffEnergy.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-cutoffkernel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.cutoffKernel"),
                H("cutoffKernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged.")),
                    Paragraph(Text("Exact uncompiled source signature: def cutoffKernel (ε s : ℝ) : ℝ :=\n  if ε < |s| then density |s| else 0\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.imageKernel.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-actual-density-tail-integrable"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.actual_density_tail_integrable"),
                H("actual density tail integrable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_density_tail_integrable {ε : ℝ} (hε : 0 < ε) :\n    IntegrableOn density (Ioi ε)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.SmoothCutoff.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-imagekernel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.imageKernel"),
                H("imageKernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged.")),
                    Paragraph(Text("Exact uncompiled source signature: def imageKernel (d ε x y : ℝ) : ℝ :=\n  ∑' m : ℤ, if m = 0 then 0 else cutoffKernel ε (x - y + m • d)\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.actual_common_cutoff_integrable_and_identity.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-zerocutoffenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.zeroCutoffEnergy"),
                H("zeroCutoffEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged.")),
                    Paragraph(Text("Exact uncompiled source signature: def zeroCutoffEnergy (d t ε : ℝ) (u : ℝ → ℂ) : ℝ :=\n  ∫ s in Ioi ε, density s * zeroTranslationEnergy d t u s\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.actual_common_cutoff_integrable_and_identity.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-periodiccutoffenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.periodicCutoffEnergy"),
                H("periodicCutoffEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged.")),
                    Paragraph(Text("Exact uncompiled source signature: def periodicCutoffEnergy (d t ε : ℝ) [Fact (0 < d)] (u : ℝ → ℂ) : ℝ :=\n  ∫ s in Ioi ε, density s * periodicTranslationEnergy d t u s\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage, D5.S3.Weil.ZetaGamma.FormCore.CommonCutoff.actual_common_cutoff_integrable_and_identity.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-actual-common-cutoff-integrable-and-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.actual_common_cutoff_integrable_and_identity"),
                H("actual common cutoff integrable and identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_common_cutoff_integrable_and_identity\n    (d t ε : ℝ) [Fact (0 < d)] (hε : 0 < ε) (u : ℝ → ℂ)\n    (hu : MemLp u 2 (windowMeasure d t)) :\n    IntegrableOn (fun s => density s * zeroTranslationEnergy d t u s) (Ioi ε) ∧\n    IntegrableOn (fun s => density s * periodicTranslationEnergy d t u s) (Ioi ε) ∧\n    Integrable (fun p : ℝ × ℝ =>\n      conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2)\n      ((windowMeasure d t).prod (windowMeasure d t)) ∧\n    zeroCutoffEnergy d t ε u = periodicCutoffEnergy d t ε u +\n      (∫ p : ℝ × ℝ,\n        conj (u p.1) * (imageKernel d ε p.1 p.2 : ℂ) * u p.2\n          ∂((windowMeasure d t).prod (windowMeasure d t))).re")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
