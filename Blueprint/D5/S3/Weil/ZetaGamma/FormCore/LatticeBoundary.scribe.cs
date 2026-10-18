using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class LatticeBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a>0 and original interval MemLp 2 inputs, both nearest images and all images with |m|>=2 are retained. The latter have an actual summable exponential majorant. Their combination proves absolute integrability and dominated convergence of the full image pairing as epsilon decreases to zero. The public natural-cutoff limit uses epsilon_n=1/(n+1) on the original Ioc carrier.",
        H("Actual Gamma form core: LatticeBoundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-latticeboundary-actualiocboundarypair"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair"),
                H("actualIocBoundaryPair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a>0 and original interval MemLp 2 inputs, both nearest images and all images with |m|>=2 are retained. The latter have an actual summable exponential majorant. Their combination proves absolute integrability and dominated convergence of the full image pairing as epsilon decreases to zero. The public natural-cutoff limit uses epsilon_n=1/(n+1) on the original Ioc carrier.")),
                    Paragraph(Text("Exact uncompiled source signature: def actualIocBoundaryPair (a ε : ℝ) (u : ℝ → ℂ) : ℝ :=\n  (∫ p : ℝ × ℝ, conj (u p.1) *\n    ((∑' m : ℤ, if m = 0 then 0 else\n      if ε < |p.1 - p.2 + m • (2 * a)| then\n        actualDensity |p.1 - p.2 + m • (2 * a)| else 0) : ℂ) * u p.2\n    ∂(volume.restrict (Ioc (-a) a)).prod (volume.restrict (Ioc (-a) a))).re\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage, D5.S3.Weil.ZetaGamma.FormCore.Corner.actualIocBoundaryPair_nat_tendsto.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-latticeboundary-actualiocboundarypair-nat-tendsto"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/LatticeBoundary.actualIocBoundaryPair_nat_tendsto"),
                H("actualIocBoundaryPair nat tendsto"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a>0 and original interval MemLp 2 inputs, both nearest images and all images with |m|>=2 are retained. The latter have an actual summable exponential majorant. Their combination proves absolute integrability and dominated convergence of the full image pairing as epsilon decreases to zero. The public natural-cutoff limit uses epsilon_n=1/(n+1) on the original Ioc carrier.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actualIocBoundaryPair_nat_tendsto (a : ℝ) (ha : 0 < a)\n    {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioc (-a) a))) :\n    Tendsto\n      (fun n : ℕ => actualIocBoundaryPair a (1 / ((n : ℝ) + 1)) u)\n      atTop (𝓝 (actualIocBoundaryPair a 0 u))")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.DomainPassage.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
