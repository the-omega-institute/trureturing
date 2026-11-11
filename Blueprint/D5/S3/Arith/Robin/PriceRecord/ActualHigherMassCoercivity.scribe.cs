using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualHigherMassCoercivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal complete higher loss controls every actual higher mass.",
        H("Literal complete higher loss controls every actual higher mass"),
        Blocks(
            Paragraph(Text("For every real X>=exp(2) and every natural n>=1, R is literally actualDefect(X,n)-completeFirstLayerLoss(X,n). The common finite dual set includes coordinates(n) and the entire low-price canonical inventory. The exact all-support identity and both dual signs yield Delta<=R X log X/s+400s sqrt X log X+400log^2 X. For R>0 the source chooses precisely s=min(1/2,sqrt(R sqrt X)). For R=0 an actual epsilon argument proves the discrete 400log^2 X remainder without any continuity of strict inventory or exclusion of ties. These steps yield constant 1000 with no record premise, exponent cap, response assumption, RH or PNT estimate on the finite proof path.")),
            Describe.Lean(
                DescribeId.Create("actualhighermasscoercivity-actual-dual-estimate"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_dual_estimate"),
                H("actual dual estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem actual_dual_estimate {X s : ℝ} (hX : exp 2 ≤ X) {n : ℕ} (hn : 1 ≤ n) (hs : 0 < s) (hs2 : s ≤ 1 / 2) : |higherMass n - higherMass (strictInteger (referencePrice X))| ≤ (actualDefect X n - completeFirstLayerLoss X n) * X * log X / s + 400 * s * sqrt X * log X + 400 * log X ^ 2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualhighermasscoercivity-balance-response"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.balance_response"),
                H("balance response"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem balance_response {Δ R q L : ℝ} (hR : 0 ≤ R) (hq : 0 < q) (hL : 0 < L) (hbound : ∀ s : ℝ, 0 < s → s ≤ 1 / 2 → Δ ≤ R * q ^ 2 * L / s + 400 * s * q * L + 400 * L ^ 2) : Δ ≤ 1000 * (q * sqrt q * L * sqrt R + q ^ 2 * L * R + L ^ 2)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualhighermasscoercivity-actual-complete-higher-mass-coercivity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherMassCoercivity.actual_complete_higher_mass_coercivity"),
                H("actual complete higher mass coercivity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem actual_complete_higher_mass_coercivity {X : ℝ} (hX : exp 2 ≤ X) (n : ℕ) (hn : 1 ≤ n) : let R := actualDefect X n - completeFirstLayerLoss X n; 0 ≤ R ∧ |higherMass n - higherMass (strictInteger (referencePrice X))| ≤ 1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R + X * log X * R + log X ^ 2)"))),
                DescribeRole.Theorem)
        )));
}
