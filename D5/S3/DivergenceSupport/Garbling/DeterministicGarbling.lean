/- GID: D5/S3/DivergenceSupport/Garbling/DeterministicGarbling
   generality: I
   mirror-B: D5/B/S3/DivergenceSupport/Garbling/DeterministicGarbling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic finite forgetting has nonnegative KL information loss. -/

import D5.S3.DivergenceSupport.ZeroSupportDefect
import D5.S3.Entropy.Forgetting.CapacityMonotone

/- Library-search audit trail (2026-08-17):
   * Repository searches for `Blackwell`, `garbling`, deterministic forgetting, KL pushforward,
     and data processing found the general channel theorem
     `DivergenceSupport.ZeroSupportDefect.dpi_defect_nonneg_zero_support`, but no deterministic
     pushforward specialization.
   * Pinned-mathlib `smart_search.sh` queries for deterministic finite-channel KL data processing
     and `klDiv` under measure maps returned no declaration hits.
   * Direct pinned-mathlib search found the `ENNReal`-valued measure chain rules
     `InformationTheory.klDiv_compProd_left` and `InformationTheory.klDiv_compProd_eq_add`, plus
     stochastic-matrix infrastructure, but no theorem directly closing the finite real-valued goal.
   * The proof therefore applies the repository's general DPI theorem and proves only that the
     graph of a function is a nonnegative row-stochastic channel. -/

namespace D5.S3.DivergenceSupport.Garbling.DeterministicGarbling

open D5.S3.Divergence.ClassicalDPI
open D5.S3.DivergenceSupport.ZeroSupportDefect
open D5.S3.Entropy.Forgetting.CapacityMonotone

/-- Deterministically forgetting a finite state through `f` cannot increase KL divergence.
Equivalently, the KL information lost by the induced Blackwell garbling is nonnegative. -/
theorem deterministic_forgetting_kl_loss_nonnegative {X Y : Type*}
    [Fintype X] [Fintype Y]
    (p q : X -> Real) (f : X -> Y)
    (hp : (forall x, 0 <= p x) ∧ ∑ x, p x = 1)
    (hq : (forall x, 0 <= q x) ∧ ∑ x, q x = 1)
    (hac : forall x, q x = 0 -> p x = 0) :
    klDivergence p q - klDivergence (pushforward f p) (pushforward f q) >= 0 := by
  classical
  let W : X -> Y -> Real := fun x y => if f x = y then 1 else 0
  have hW : (forall x y, 0 <= W x y) ∧ forall x, ∑ y, W x y = 1 := by
    constructor
    · intro x y
      by_cases hxy : f x = y <;> simp [W, hxy]
    · intro x
      simp [W]
  have hOutput (r : X -> Real) : channelOutput W r = pushforward f r := by
    funext y
    simp only [channelOutput, pushforward]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hxy : f x = y <;> simp [W, hxy]
  have hDpi := dpi_defect_nonneg_zero_support p q W hp hq hac hW
  rw [hOutput p, hOutput q] at hDpi
  exact hDpi

#print axioms deterministic_forgetting_kl_loss_nonnegative

end D5.S3.DivergenceSupport.Garbling.DeterministicGarbling
