using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class FrequencyDomainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a>0 and only original Ioc MemLp 2, finite zero-extension actual-Gamma energy is equivalent to finiteness of the full integer coefficient sum with the actual digamma-increment weights. This consumes the boundary-domain equivalence and periodic spectral identity, not a new Fourier-L2 premise. This retained companion result does not supply a stronger hypothesis to the compact-core endpoints.",
        H("Actual Gamma form core: FrequencyDomain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-frequencydomain-actual-gamma-zero-domain-iff-digamma-weighted-sum-finite"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actual_gamma_zero_domain_iff_digamma_weighted_sum_finite"),
                H("actual gamma zero domain iff digamma weighted sum finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a>0 and only original Ioc MemLp 2, finite zero-extension actual-Gamma energy is equivalent to finiteness of the full integer coefficient sum with the actual digamma-increment weights. This consumes the boundary-domain equivalence and periodic spectral identity, not a new Fourier-L2 premise. This retained companion result does not supply a stronger hypothesis to the compact-core endpoints.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_gamma_zero_domain_iff_digamma_weighted_sum_finite\n    (a : ℝ) (ha : 0 < a) (u : ℝ → ℂ)\n    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :\n    letI : Fact (0 < 2 * a) := ⟨by linarith⟩\n    IntegrableOn (zeroEnergyDensity (2 * a) (-a) u) (Ioi 0) ↔\n      (∑' n : ℤ,\n        ENNReal.ofReal\n          (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.gammaIncrement\n            (D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.angularFrequency\n              (d := 2 * a) n)) *\n        ENNReal.ofReal\n          (‖D5.S3.Weil.ZetaGamma.FormCore.PeriodicSpectralEnergy.physicalCoeff\n            (AddCircle.liftIoc (2 * a) (-a) u) n‖ ^ 2)) < ∞")),
                    Paragraph(Text("Retained result on the delivery surface.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
