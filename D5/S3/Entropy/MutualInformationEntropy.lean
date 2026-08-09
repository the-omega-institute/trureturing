/- GID: D5/S3/Entropy/MutualInformationEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/MutualInformationEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose finite mutual information into entropies and derive subadditivity. -/

/- Library-search audit trail (2026-08-09):
   * Local pinned-mathlib grep terms: `mutualInformation`, `mutual_information`,
     `mutualInfo`, `MutualInfo`, `mutual information`, `shannonEntropy`,
     `shannon_entropy`, `finiteEntropy`, `entropy_subadditive`,
     `subadditiv.*entropy`, `klDiv.*entropy`, `entropy.*klDiv`,
     `relativeEntropy.*entropy`, `entropy.*relativeEntropy`, `klDiv.*prod`,
     `klDiv_compProd_eq_add`, `klDiv_compProd_left`, `negMulLog.*Finset`,
     `Finset.*negMulLog`, `sum_prod_type`, `sum_comm`, `sum_mul`, `mul_sum`,
     `log_div`, and `log_mul`.
   * `Mathlib.InformationTheory.KullbackLeibler.ChainRule` provides measure-valued KL
     product/chain rules, and `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` provides the
     scalar Shannon atom. No pinned finite mutual-information/Shannon-entropy decomposition or
     entropy-subadditivity theorem matching the repository's real-valued finite sums was found.
   * Repository-wide `D5/` grep covered mutual-information/entropy names in both orders;
     `shannonEntropy` adjacent to `marginal`; inequalities in both orientations; `sub_nonneg`
     forms; `negMulLog` adjacent to marginals; KL against two marginals; and the expanded
     `Real.log` summands. No duplicate or rearranged equivalent was found.
   * This identity is the general pin that `MutualInformationProduct` could not provide: it holds
     for every admissible joint, including correlated joints, and therefore constrains the
     imported mutual-information definition everywhere rather than only on product laws.
     In fact, normalization is unnecessary for the algebraic identity, so its theorem assumes
     only pointwise nonnegativity; subadditivity restores normalization to invoke KL nonnegativity.
   * The proof works directly with the repository's `mutualInformation`, `klDivergence`,
     `marginal`, and `shannonEntropy`. Units are nats because all logarithms are `Real.log`.
-/

import D5.S3.Entropy.MaxEntropy
import D5.S3.Entropy.MutualInformation

namespace D5.S3.Entropy.MutualInformationEntropy

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation

/-- Mutual information is the sum of the marginal entropies minus the joint entropy. -/
theorem mutual_information_eq_entropy_sub {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : ∀ x, 0 ≤ p x) :
    mutualInformation p =
      shannonEntropy (marginal p) +
        shannonEntropy (marginal (fun r : κ × ι => p (r.2, r.1))) -
          shannonEntropy p := by
  classical
  let m₁ : ι → ℝ := marginal p
  let m₂ : κ → ℝ := marginal (fun r : κ × ι => p (r.2, r.1))
  have hterm (i : ι) (j : κ) :
      p (i, j) * Real.log (p (i, j) / (m₁ i * m₂ j)) =
        -Real.negMulLog (p (i, j)) +
          (-(p (i, j) * Real.log (m₁ i))) +
            (-(p (i, j) * Real.log (m₂ j))) := by
    by_cases hpij : p (i, j) = 0
    · simp [hpij]
    · have hpij_pos : 0 < p (i, j) :=
        lt_of_le_of_ne (hp (i, j)) (Ne.symm hpij)
      have hm₁_pos : 0 < m₁ i := by
        apply lt_of_lt_of_le hpij_pos
        change p (i, j) ≤ ∑ j', p (i, j')
        exact Finset.single_le_sum
          (fun j' _ => hp (i, j')) (Finset.mem_univ j)
      have hm₂_pos : 0 < m₂ j := by
        apply lt_of_lt_of_le hpij_pos
        change p (i, j) ≤ ∑ i', p (i', j)
        exact Finset.single_le_sum
          (fun i' _ => hp (i', j)) (Finset.mem_univ i)
      rw [Real.log_div hpij (mul_ne_zero (ne_of_gt hm₁_pos) (ne_of_gt hm₂_pos))]
      rw [Real.log_mul (ne_of_gt hm₁_pos) (ne_of_gt hm₂_pos)]
      simp only [Real.negMulLog]
      ring
  have hjoint :
      (∑ i, ∑ j, -Real.negMulLog (p (i, j))) = -shannonEntropy p := by
    rw [shannonEntropy, Fintype.sum_prod_type]
    calc
      (∑ i, ∑ j, -Real.negMulLog (p (i, j))) =
          ∑ i, -(∑ j, Real.negMulLog (p (i, j))) := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_neg_distrib fun j => Real.negMulLog (p (i, j))
      _ = -(∑ i, ∑ j, Real.negMulLog (p (i, j))) := by
            exact Finset.sum_neg_distrib fun i =>
              ∑ j, Real.negMulLog (p (i, j))
  have hfirst :
      (∑ i, ∑ j, -(p (i, j) * Real.log (m₁ i))) = shannonEntropy m₁ := by
    rw [shannonEntropy]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (∑ j, -(p (i, j) * Real.log (m₁ i))) =
          -(∑ j, p (i, j) * Real.log (m₁ i)) := by
            rw [Finset.sum_neg_distrib]
      _ = -((∑ j, p (i, j)) * Real.log (m₁ i)) := by
            rw [Finset.sum_mul]
      _ = -(m₁ i * Real.log (m₁ i)) := by rfl
      _ = Real.negMulLog (m₁ i) := by
            simp only [Real.negMulLog]
            ring
  have hsecond :
      (∑ i, ∑ j, -(p (i, j) * Real.log (m₂ j))) = shannonEntropy m₂ := by
    rw [Finset.sum_comm, shannonEntropy]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (∑ i, -(p (i, j) * Real.log (m₂ j))) =
          -(∑ i, p (i, j) * Real.log (m₂ j)) := by
            rw [Finset.sum_neg_distrib]
      _ = -((∑ i, p (i, j)) * Real.log (m₂ j)) := by
            rw [Finset.sum_mul]
      _ = -(m₂ j * Real.log (m₂ j)) := by rfl
      _ = Real.negMulLog (m₂ j) := by
            simp only [Real.negMulLog]
            ring
  have hsum :
      klDivergence p (fun q => m₁ q.1 * m₂ q.2) =
        shannonEntropy m₁ + shannonEntropy m₂ - shannonEntropy p := by
    rw [klDivergence]
    simp only [Fintype.sum_prod_type]
    calc
      (∑ i, ∑ j, p (i, j) * Real.log (p (i, j) / (m₁ i * m₂ j))) =
          ∑ i, ∑ j,
            (-Real.negMulLog (p (i, j)) +
              (-(p (i, j) * Real.log (m₁ i))) +
                (-(p (i, j) * Real.log (m₂ j)))) := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_congr rfl fun j _ => hterm i j
      _ = (∑ i, ∑ j, -Real.negMulLog (p (i, j))) +
            (∑ i, ∑ j, -(p (i, j) * Real.log (m₁ i))) +
              (∑ i, ∑ j, -(p (i, j) * Real.log (m₂ j))) := by
            simp_rw [Finset.sum_add_distrib]
      _ = shannonEntropy m₁ + shannonEntropy m₂ - shannonEntropy p := by
            rw [hjoint, hfirst, hsecond]
            ring
  simpa only [mutualInformation, m₁, m₂] using hsum

/-- Shannon entropy is subadditive under finite marginalization. -/
theorem entropy_subadditive {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι × κ → ℝ) (hp : (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    shannonEntropy p ≤
      shannonEntropy (marginal p) +
        shannonEntropy (marginal (fun r : κ × ι => p (r.2, r.1))) := by
  have hmi := mutual_information_nonneg p hp
  rw [mutual_information_eq_entropy_sub p hp.1] at hmi
  exact sub_nonneg.mp hmi

end D5.S3.Entropy.MutualInformationEntropy
