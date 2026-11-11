using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualHigherMassCoercivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal complete higher loss controls every actual higher mass.",
        H("Literal complete higher loss controls every actual higher mass"),
        Blocks(
            Paragraph(Text("SOURCE ONLY: UNCOMPILED_UNACCEPTED. No Lean elaboration, kernel/axiom closure, native report, Scribe compilation, official acceptance, or four-slot Reg validation was run. Full Lean bodies are candidate proof attempts. The ordinary Pro derivation and the independent ordinary audit are fallible inputs, not axioms; this context already includes the repository and prior source candidates. No sterile-context or model-diversity claim is made. Native checking may expose elaboration or proof gaps. Root owns both pre-existing native queues and later integration.")),
            Paragraph(Text("For every real X>=exp(2) and every natural n>=1, R is literally actualDefect(X,n)-completeFirstLayerLoss(X,n). The common finite dual set includes coordinates(n) and the entire low-price canonical inventory. The exact all-support identity and both dual signs yield Delta<=R X log X/s+400s sqrt X log X+400log^2 X. For R>0 the source chooses precisely s=min(1/2,sqrt(R sqrt X)). For R=0 an actual epsilon argument proves the discrete 400log^2 X remainder without any continuity of strict inventory or exclusion of ties. These steps yield constant 1000 with no record premise, exponent cap, response assumption, RH or PNT estimate on the finite proof path.")),
            Paragraph(Text("Owning Lean source SHA256: cc45bc337dd66d9b40b5eca7fc00d456a6ab361d743a6b1c6c0a81d7bd692bab. The complete new-declaration signatures, source line locations, import closure and dependency patches are exposed in source-manifest.json and dependency-boundary.json.")),
            Paragraph(Text("Four-slot Reg is not supplied. Missing evidence after the compiled telescope is an actual full-law variation/realization for this literal prime-power inventory, an exact specialization/control witness on its valid arithmetic domain, the corresponding realization/equivalence proofs, and the residual/open-slot statement accepted by the current Reg contract. Abstract invented spectra, weakened prime support or assumed final inequalities would not be faithful. Root must attach that precise missing-evidence statement to its existing issue workflow after native compilation; no issue or fake declared_validated status is created in this source-only packet.")),
            Describe.Lean(
                DescribeId.Create("actualhighermasscoercivity-actual-dual-estimate"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_dual_estimate"),
                H("actual dual estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem actual_dual_estimate {X s : ℝ} (hX : exp 2 ≤ X) {n : ℕ} (hn : 1 ≤ n)\n    (hs : 0 < s) (hs2 : s ≤ 1 / 2) :\n    |higherMass n - higherMass (strictInteger (referencePrice X))| ≤\n      (actualDefect X n - completeFirstLayerLoss X n) * X * log X / s +\n        400 * s * sqrt X * log X + 400 * log X ^ 2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualhighermasscoercivity-balance-response"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.balance_response"),
                H("balance response"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem balance_response {Δ R q L : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hL : 0 < L)\n    (hbound : ∀ s : ℝ, 0 < s → s ≤ 1 / 2 →\n      Δ ≤ R * q ^ 2 * L / s + 400 * s * q * L + 400 * L ^ 2) :\n    Δ ≤ 1000 * (q * sqrt q * L * sqrt R + q ^ 2 * L * R + L ^ 2)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualhighermasscoercivity-actual-complete-higher-mass-coercivity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_complete_higher_mass_coercivity"),
                H("actual complete higher mass coercivity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem actual_complete_higher_mass_coercivity {X : ℝ} (hX : exp 2 ≤ X)\n    (n : ℕ) (hn : 1 ≤ n) :\n    let R := actualDefect X n - completeFirstLayerLoss X n\n    0 ≤ R ∧\n    |higherMass n - higherMass (strictInteger (referencePrice X))| ≤\n      1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R + X * log X * R + log X ^ 2)"))),
                DescribeRole.Theorem)
        )));
}
