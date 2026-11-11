using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class HigherLossScalarAbsorptionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact sharp scalar reduction and two Young bounds.",
        H("Exact sharp scalar reduction and two Young bounds"),
        Blocks(
            Paragraph(Text("SOURCE ONLY: UNCOMPILED_UNACCEPTED. No Lean elaboration, kernel/axiom closure, native report, Scribe compilation, official acceptance, or four-slot Reg validation was run. Full Lean bodies are candidate proof attempts. The ordinary Pro derivation and the independent ordinary audit are fallible inputs, not axioms; this context already includes the repository and prior source candidates. No sterile-context or model-diversity claim is made. Native checking may expose elaboration or proof gaps. Root owns both pre-existing native queues and later integration.")),
            Paragraph(Text("The finite budget 6VW/(X^2 log(X/2))+delta/(X log X), V<=T, W<=Delta+delta, delta<=2log X, and the already proved coercivity yield R<=a T sqrt(R)/X^(5/4)+a(T/X)R+dTlog X/X^2+2/X, with a=12000 and d=24000. Taking T=E+5sqrt X, coarse sublinearity makes aT/X<=1/4. The square (sqrt R/2-aT/X^(5/4))^2 absorbs the square-root term. A second Young square absorbs Tlog X/X^2. The log-squared rounding term is <=1/X eventually, proved through a standard logarithmic little-o limit. q=2a^2+d and finalConstant=52q+d+4 give the exact E^2/X^(5/2)+1/X rate. These scalar implications are consumed by the actual constructed record application; they are not final-bound assumptions.")),
            Paragraph(Text("Owning Lean source SHA256: 08a23d73821d707adcd013fad6246fdcfd457d44587f6283b56481d1e3900b6f. The complete new-declaration signatures, source line locations, import closure and dependency patches are exposed in source-manifest.json and dependency-boundary.json.")),
            Paragraph(Text("Four-slot Reg is not supplied. Missing evidence after the compiled telescope is an actual full-law variation/realization for this literal prime-power inventory, an exact specialization/control witness on its valid arithmetic domain, the corresponding realization/equivalence proofs, and the residual/open-slot statement accepted by the current Reg contract. Abstract invented spectra, weakened prime support or assumed final inequalities would not be faithful. Root must attach that precise missing-evidence statement to its existing issue workflow after native compilation; no issue or fake declared_validated status is created in this source-only packet.")),
            Describe.Lean(
                DescribeId.Create("higherlossscalarabsorption-scalar-budget-reduction"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_budget_reduction"),
                H("scalar budget reduction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem scalar_budget_reduction {X T V W Δ δ R : ℝ}\n    (hX : exp 2 ≤ X) (hT : 0 ≤ T) (hV : 0 ≤ V) (hW : 0 ≤ W)\n    (hVT : V ≤ T) (hWΔ : W ≤ Δ + δ) (hδ0 : 0 ≤ δ)\n    (hδ : δ ≤ 2 * log X) (hhalf : log X / 2 ≤ log (X / 2))\n    (hR : R ≤ 6 * V * W / (X ^ 2 * log (X / 2)) + δ / (X * log X))\n    (hΔ : Δ ≤ 1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R +\n      X * log X * R + log X ^ 2)) :\n    R ≤ a * T / X ^ (5 / 4 : ℝ) * sqrt R + a * (T / X) * R +\n      d * T * log X / X ^ 2 + 2 / X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlossscalarabsorption-scalar-absorption"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_absorption"),
                H("scalar absorption"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem scalar_absorption {X E R : ℝ} (hX : 1 < X) (hE : 0 ≤ E) (hR0 : 0 ≤ R)\n    (hsmall : a * ((E + 5 * sqrt X) / X) ≤ 1 / 4)\n    (hlog : log X ^ 2 ≤ sqrt X)\n    (hR : R ≤ a * (E + 5 * sqrt X) / X ^ (5 / 4 : ℝ) * sqrt R +\n      a * ((E + 5 * sqrt X) / X) * R +\n      d * (E + 5 * sqrt X) * log X / X ^ 2 + 2 / X) :\n    R ≤ finalConstant * (E ^ 2 / X ^ (5 / 2 : ℝ) + 1 / X)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlossscalarabsorption-log-rounding-eventually"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.log_rounding_eventually"),
                H("log rounding eventually"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem log_rounding_eventually : ∀ᶠ X : ℝ in atTop, log X ^ 2 ≤ sqrt X"))),
                DescribeRole.Theorem)
        )));
}
