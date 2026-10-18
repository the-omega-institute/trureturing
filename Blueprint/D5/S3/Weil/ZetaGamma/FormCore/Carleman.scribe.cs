using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class CarlemanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex u and v satisfy MemLp 2 on the actual positive Lebesgue half-line. No double-integrability, row-bound or operator-bound premise is supplied. The actual r^(-1/2) row integral, weighted Young inequality, balancing and the zero-energy AE cases prove absolute integrability and the pi times product-of-L2-norms bound. This is the classical Carleman inequality, reused as a live corner estimate; no novelty claim.",
        H("Actual Gamma form core: Carleman"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-carleman-carleman-integrable-and-integral-le"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/Carleman.carleman_integrable_and_integral_le"),
                H("carleman integrable and integral le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Complex u and v satisfy MemLp 2 on the actual positive Lebesgue half-line. No double-integrability, row-bound or operator-bound premise is supplied. The actual r^(-1/2) row integral, weighted Young inequality, balancing and the zero-energy AE cases prove absolute integrability and the pi times product-of-L2-norms bound. This is the classical Carleman inequality, reused as a live corner estimate; no novelty claim.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem carleman_integrable_and_integral_le\n    {u v : ℝ → ℂ}\n    (hu : MemLp u 2 (volume.restrict (Ioi 0)))\n    (hv : MemLp v 2 (volume.restrict (Ioi 0))) :\n    Integrable (fun p : ℝ × ℝ => ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2))\n      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧\n    (∫ p : ℝ × ℝ, ‖u p.1‖ * ‖v p.2‖ / (p.1 + p.2)\n      ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ≤\n      Real.pi * Real.sqrt (∫ r, ‖u r‖ ^ 2 ∂volume.restrict (Ioi 0)) *\n        Real.sqrt (∫ s, ‖v s‖ ^ 2 ∂volume.restrict (Ioi 0))")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CornerTransport.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
