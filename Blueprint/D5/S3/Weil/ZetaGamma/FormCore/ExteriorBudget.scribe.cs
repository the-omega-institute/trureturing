using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

// SOURCE_ONLY_UNCOMPILED. Definition source only; no generated Markdown.
internal sealed class ExteriorBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The jump measure is the positive-half-line Lebesgue measure withDensity ofReal(rho). For an interior point its ENNReal exit potential equals ofReal of the two actual Gamma tails at a-y and a+y. Finite actual directional energy and zero support outside Ioo(-a,a) control the exterior-weighted L2 mass. The proof does not assume an independent boundary or endpoint budget.",
        H("Actual Gamma form core: ExteriorBudget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-exteriorbudget-actualgammaexitmeasure"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ExteriorBudget.actualGammaExitMeasure"),
                H("actualGammaExitMeasure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The jump measure is the positive-half-line Lebesgue measure withDensity ofReal(rho). For an interior point its ENNReal exit potential equals ofReal of the two actual Gamma tails at a-y and a+y. Finite actual directional energy and zero support outside Ioo(-a,a) control the exterior-weighted L2 mass. The proof does not assume an independent boundary or endpoint budget.")),
                    Paragraph(Text("Exact uncompiled source signature: abbrev actualGammaExitMeasure : Measure ℝ :=\n  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (actualDensity s))\n")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence, D5.S3.Weil.ZetaGamma.FormCore.InteriorApproximation, D5.S3.Weil.ZetaGamma.FormCore.Mollifier, D5.S3.Weil.ZetaGamma.FormCore.SmoothCore, D5.S3.Weil.ZetaGamma.FormCore.EvenCore, D5.S3.Weil.ZetaGamma.FormCore.actual_gamma_exteriorPotential_eq_ofReal.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-exteriorbudget-actual-gamma-exteriorpotential-eq-ofreal"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ExteriorBudget.actual_gamma_exteriorPotential_eq_ofReal"),
                H("actual gamma exteriorPotential eq ofReal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The jump measure is the positive-half-line Lebesgue measure withDensity ofReal(rho). For an interior point its ENNReal exit potential equals ofReal of the two actual Gamma tails at a-y and a+y. Finite actual directional energy and zero support outside Ioo(-a,a) control the exterior-weighted L2 mass. The proof does not assume an independent boundary or endpoint budget.")),
                    Paragraph(Text("Exact uncompiled source signature: theorem actual_gamma_exteriorPotential_eq_ofReal {a y : ℝ}\n    (hy : y ∈ Ioo (-a) a) :\n    exteriorPotential actualGammaExitMeasure (Ioo (-a) a) y =\n      ENNReal.ofReal (actualExteriorPotential a y)")),
                    Paragraph(Text("Consumed helper on the retained proof path; consumers: D5.S3.Weil.ZetaGamma.FormCore.CutoffConvergence.")),
                    Paragraph(Text("Source provenance: exact stitched input SHA256 e122c32598b4ae28c34f6aff62d86297165f4a5c77916d19657e9fd13552d5b7; stable namespace/import/visibility repackaging only, except the explicitly recorded canonical transport API application. This is repository-exposed material, not an independent implementation or a mathematical novelty claim.")),
                    Paragraph(Text("SOURCE_ONLY_UNCOMPILED: the exact input acceptance does not transfer to this declaration. Lean elaboration, kernel/axiom closure, Scribe emission, Reg source binding and required checks remain unrun. No closed-form realization, full signed Weil-form positivity or RH consequence is asserted."))),
                DescribeRole.Theorem))));
}
