using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class TwoFixedLayerPrefixBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "TwoFixedLayerPrefixBudget",
        H("D5 and Reg sources compile; RegUNVALIDATED audit"),
        Blocks(
            Paragraph(Text("The 2/3 ledger specializes the new arbitrary-layer construction and has no D5 proof consumer. The live 2/4 repair uses two_roster_integer_ledger_at_layers at 2,4. The seeded 2/3 coefficient endpoint and finite paid comparison remain separate substantive results.")),
            Paragraph(Text("The D5 and Reg source targets compile under the scoped Lean checks. The Reg escape audit remains unvalidated for kernel/axiom closure, lawful enrollment, source binding and official/RH acceptance; no novelty or consensus claim is asserted. Ordinary Pro reasoning is fallible input. The final uniform paid-prefix repair, its uniform original-price consumer, and the optional elementary-energy consumer remain unfinished. The finite components must not be presented as those final theorems. Existing owners are imported with exact unapplied consumed-helper patches. Each public target has a faithful full-telescope typed Reg attempt; rejected lawful families, whole-family variation, sensitivity, observational dependence and exact source binding remain missing.")),
            Describe.Lean(
                DescribeId.Create("twofixedlayerprefixbudget-seeded-two-layer-coefficients"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.seeded_two_layer_coefficients"),
                H("seeded two layer coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem seeded_two_layer_coefficients :     ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, ∃ C T : ℝ, 0 < C ∧ 1 < T ∧       ∀ X : ℝ, T ≤ X → ∀ δ₀ f : ℝ,         0 ≤ δ₀ → δ₀ ≤ log (2 * X) → f ∈ Set.Icc (X / 2) (2 * X) →         ∃ a b : ℕ, b ≤ B ∧ (a + b : ℝ) ≤ C * log X ∧           log X - log 2 ≤ δ₀ + log f ∧           δ₀ + log f ≤ 2 * log X + 2 * log 2 ∧           δ₀ + log f - ε / 2 ≤             (a : ℝ) * (2 * log (cutoff 2 (referencePrice X)) - log X) +             (b : ℝ) * (3 * log (cutoff 3 (referencePrice X)) - log X) ∧           (a : ℝ) * (2 * log (cutoff 2 (referencePrice X)) - log X) +             (b : ℝ) * (3 * log (cutoff 3 (referencePrice X)) - log X) ≤               δ₀ + log f - ε / 4"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twofixedlayerprefixbudget-two-roster-integer-ledger"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.two_roster_integer_ledger"),
                H("two roster integer ledger"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem two_roster_integer_ledger {X : ℝ} (hX : 4 < X) {Q : ℕ}     (hQ2 : 2 ≤ Q) (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))     {r : ℝ} (hr : r ∈ Set.Icc (X / 2) (2 * X))     (hroot : firstLayerPrice r = referencePrice X)     (hsupport : ∀ p : ℕ, p.Prime →       2 ≤ (strictInteger (referencePrice X)).factorization p → p ≤ Q)     (A₂ A₃ : Finset ℕ) (hdis : Disjoint A₂ A₃)     (hA₂ : ∀ p ∈ A₂, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = 1)     (hA₃ : ∀ p ∈ A₃, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = 2) :     let n := strictInteger (referencePrice X)     let base := higherCore n * prefixInteger Q     let k := base * (∏ p ∈ A₂, p) * (∏ p ∈ A₃, p)     2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧       (∀ p : ℕ, k.factorization p =         base.factorization p + (if p ∈ A₂ then 1 else 0) + (if p ∈ A₃ then 1 else 0)) ∧       log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) +         (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧       log (higherCore k : ℝ) = log (higherCore n : ℝ) +         (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧       actualDefect X k - completeFirstLayerLoss X k =         (∑ p ∈ A₂, (referencePrice X - goldenLayerMarginal p 2) * log p) +         (∑ p ∈ A₃, (referencePrice X - goldenLayerMarginal p 3) * log p) ∧       (∀ p : ℕ, p.Prime → p ∉ A₂ ∪ A₃ → ∀ j : ℕ, 2 ≤ j →         (j ≤ k.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p))"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twofixedlayerprefixbudget-finite-paid-prefix-comparison"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.finite_paid_prefix_comparison"),
                H("finite paid prefix comparison"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem finite_paid_prefix_comparison {η X μ : ℝ} (hX : 4 < X)     {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)     (hrecord : ∀ a : ℕ, 0 < a → a < m →       goldenResourceObjective μ a < goldenResourceObjective μ m)     (hclock : X = log (m : ℝ))     (hP : (largestPrime m : ℝ) ∈ Set.Icc (X / 2) (2 * X))     (b : Budget) (hb : b.spec X)     (hslack : 0 ≤ X - log (k : ℝ))     (hpaid : |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| +       (actualDefect X k - completeFirstLayerLoss X k) +         referencePrice X * (X - log (k : ℝ)) ≤ η / (X * log X)) :     k ≤ m ∧ 0 ≤ actualDefect X m - completeFirstLayerLoss X m ∧       actualDefect X m - completeFirstLayerLoss X m + μ * (X - log (k : ℝ)) ≤         η / (X * log X) +         6 * max (|(largestPrime m : ℝ) - b.r|) (|(b.Q : ℝ) - b.r|) *           |b.h + b.δ - (log (m : ℝ) - Chebyshev.theta (largestPrime m : ℝ))| /             (X ^ 2 * log (X / 2))"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twofixedlayerprefixbudget-residual-nonneg"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.residual_nonneg"),
                H("residual nonneg"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem residual_nonneg {X : ℝ} (hX : 1 < X) {n : ℕ} (hn : 1 ≤ n) :     0 ≤ actualDefect X n - completeFirstLayerLoss X n"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twofixedlayerprefixbudget-insert-roster-at-prefix"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.insert_roster_at_prefix"),
                H("insert roster at prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem insert_roster_at_prefix {X : ℝ} (hX : 4 < X) {base Q : ℕ}     (hb2 : 2 ≤ base) (hpref : base.primeFactors = Nat.primesLE Q)     (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X)) {r : ℝ}     (hr : r ∈ Set.Icc (X / 2) (2 * X))     (hroot : firstLayerPrice r = referencePrice X)     {J : ℕ} (hJ : 1 ≤ J) (A : Finset ℕ)     (hA : ∀ p ∈ A, p.Prime ∧ p ≤ Q ∧ base.factorization p = J - 1) :     let k := base * ∏ p ∈ A, p     2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧       log (k : ℝ) - log (base : ℝ) = ∑ p ∈ A, log p ∧       (∀ p, k.factorization p = base.factorization p + if p ∈ A then 1 else 0) ∧       actualDefect X k - completeFirstLayerLoss X k =         (actualDefect X base - completeFirstLayerLoss X base) +           ∑ p ∈ A, (referencePrice X - goldenLayerMarginal p J) * log p"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twofixedlayerprefixbudget-two-price-compare"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherLayerBudgetRepair.two_price_compare"),
                H("two price compare"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem two_price_compare {X μ : ℝ} {m k : ℕ}     (hm : 2 ≤ m) (hk : 2 ≤ k) (hμ : 0 < μ)     (hrecord : ∀ a : ℕ, 0 < a → a < m →       goldenResourceObjective μ a < goldenResourceObjective μ m)     (hclock : X = log (m : ℝ)) (hslack : 0 ≤ X - log (k : ℝ)) :     k ≤ m ∧ actualDefect X m - actualDefect X k ≤       (referencePrice X - μ) * (X - log (k : ℝ))"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("twofixedlayerprefixbudget-prefix-budget-integer"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualRecordAllLogBudgetRemainder.prefix_budget_integer"),
                H("prefix budget integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem prefix_budget_integer {n Q : ℕ} (hQ : 2 ≤ Q)     (hsupport : ∀ p : ℕ, p.Prime → 2 ≤ n.factorization p → p ≤ Q) :     let k := higherCore n * prefixInteger Q     2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧     log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) ∧     ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →       (j ≤ k.factorization p ↔ j ≤ n.factorization p)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-two-roster-integer-ledger-at-layers"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/TwoFixedLayerPrefixBudget.two_roster_integer_ledger_at_layers"),
                H("two_roster_integer_ledger_at_layers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D5 compiled / RegUNVALIDATED. Exact full candidate statement: theorem two_roster_integer_ledger_at_layers {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)     {X : ℝ} (hX : 4 < X) {Q : ℕ}     (hQ2 : 2 ≤ Q) (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))     {r : ℝ} (hr : r ∈ Set.Icc (X / 2) (2 * X))     (hroot : firstLayerPrice r = referencePrice X)     (hsupport : ∀ p : ℕ, p.Prime →       2 ≤ (strictInteger (referencePrice X)).factorization p → p ≤ Q)     (A₂ A₃ : Finset ℕ) (hdis : Disjoint A₂ A₃)     (hA₂ : ∀ p ∈ A₂, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = i - 1)     (hA₃ : ∀ p ∈ A₃, p.Prime ∧ p ≤ Q ∧ optimalLayerCount (referencePrice X) p = j - 1) :     let n := strictInteger (referencePrice X)     let base := higherCore n * prefixInteger Q     let k := base * (∏ p ∈ A₂, p) * (∏ p ∈ A₃, p)     2 ≤ k ∧ k.primeFactors = Nat.primesLE Q ∧       (∀ p : ℕ, k.factorization p =         base.factorization p + (if p ∈ A₂ then 1 else 0) + (if p ∈ A₃ then 1 else 0)) ∧       log (k : ℝ) = log (higherCore n : ℝ) + Chebyshev.theta (Q : ℝ) +         (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧       log (higherCore k : ℝ) = log (higherCore n : ℝ) +         (∑ p ∈ A₂, log p) + (∑ p ∈ A₃, log p) ∧       actualDefect X k - completeFirstLayerLoss X k =         (∑ p ∈ A₂, (referencePrice X - goldenLayerMarginal p i) * log p) +         (∑ p ∈ A₃, (referencePrice X - goldenLayerMarginal p j) * log p) ∧       (∀ p : ℕ, p.Prime → p ∉ A₂ ∪ A₃ → ∀ l : ℕ, 2 ≤ l →         (l ≤ k.factorization p ↔ l ≤ optimalLayerCount (referencePrice X) p))"))),
                DescribeRole.Theorem)
        )));
}
