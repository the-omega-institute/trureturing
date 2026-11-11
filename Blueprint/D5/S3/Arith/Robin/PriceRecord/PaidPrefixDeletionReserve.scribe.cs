using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class PaidPrefixDeletionReserveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "PaidPrefixDeletionReserve",
        H("D5 source compiled; RegUNVALIDATED components"),
        Blocks(
            Paragraph(Text("The d=1 endpoint specializes the new all-d power construction and has no D5 proof consumer. The live 2/4 repair uses budget_prefix_deletion_reserve_power at d=2; expanding the endpoint reaches that new construction, so short specialization syntax alone is not a bind-only classification.")),
            Paragraph(Text("The D5 source target has a current scoped Lean build. Retained Reg sources compile with standard axiom closure; lawful enrollment and source binding remain incomplete; no novelty or consensus claim is asserted. Ordinary Pro reasoning is fallible input. These components feed the separate actual two/four paid-prefix repair. The uniform original-price and optional elementary-energy endgoals remain open. Existing owners are imported with visibility-only consumed-helper exposures. Each public target has a faithful full-telescope typed Reg attempt; rejected lawful families, whole-family variation, sensitivity, observational dependence and exact source binding remain missing.")),
            Describe.Lean(
                DescribeId.Create("paidprefixdeletionreserve-budget-prefix-deletion-reserve"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.budget_prefix_deletion_reserve"),
                H("budget prefix deletion reserve"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem budget_prefix_deletion_reserve :     ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧       ∀ X : ℝ, T ≤ X → ∀ b : Budget, b.spec X →       ∀ M : ℕ, (M : ℝ) ≤ C * log X →         ∃ Q : ℕ, ∃ D : Finset ℕ, Q.Prime ∧ X / 2 < (Q : ℝ) ∧ Q ≤ b.Q ∧           D = Nat.primesLE b.Q \\ Nat.primesLE Q ∧ D.card = M ∧           (∀ p ∈ D, p.Prime ∧ Q < p ∧ p ≤ b.Q) ∧           Chebyshev.theta (b.Q : ℝ) - Chebyshev.theta (Q : ℝ) = ∑ p ∈ D, log p ∧           (∑ p ∈ D, log p) ≤ (M : ℝ) * log (2 * X)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("paidprefixdeletionreserve-finite-prefix-deletion-cost"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.finite_prefix_deletion_cost"),
                H("finite prefix deletion cost"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem finite_prefix_deletion_cost {X : ℝ} (hX : 4 < X)     (b : Budget) (hb : b.spec X) {Q k M : ℕ}     (hk : 2 ≤ k) (hkp : k.primeFactors = Nat.primesLE Q)     (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X)) (hQb : Q ≤ b.Q)     (D : Finset ℕ) (hD : D = Nat.primesLE b.Q \\ Nat.primesLE Q) (hDM : D.card = M) :     |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| ≤       6 * (shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X) + 1) *         ((M : ℝ) * log (2 * X)) / (X ^ 2 * log (X / 2)) ∧     (∀ f : ℝ, (Q : ℝ) ≤ f → f ≤ b.Q →       |log f - log X| ≤ (2 / X) *         (shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X)))"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-budget-prefix-deletion-reserve-power"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve.budget_prefix_deletion_reserve_power"),
                H("budget_prefix_deletion_reserve_power"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem budget_prefix_deletion_reserve_power (d : ℕ) :     ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧       ∀ X : ℝ, T ≤ X → ∀ b : Budget, b.spec X →       ∀ M : ℕ, (M : ℝ) ≤ C * log X ^ d →         ∃ Q : ℕ, ∃ D : Finset ℕ, Q.Prime ∧ X / 2 < (Q : ℝ) ∧ Q ≤ b.Q ∧           D = Nat.primesLE b.Q \\ Nat.primesLE Q ∧ D.card = M ∧           (∀ p ∈ D, p.Prime ∧ Q < p ∧ p ≤ b.Q) ∧           Chebyshev.theta (b.Q : ℝ) - Chebyshev.theta (Q : ℝ) = ∑ p ∈ D, log p ∧           (∑ p ∈ D, log p) ≤ (M : ℝ) * log (2 * X)"))),
                DescribeRole.Theorem)
        )));
}
