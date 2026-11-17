/- GID: D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualFirstLayerPrefixCancellation
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Complete prefix cancellation controls the actual record's higher loss through a finite budget comparator. -/

import D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
import D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! SOURCE CANDIDATE: UNCOMPILED_UNACCEPTED.
The accompanying patch exposes consumed original helpers without changing their proofs.
The root equation uses ActualBalancedCutoff.firstLayerPrice, not a second root definition.
No asymptotic statement, RH criterion, registration or kernel acceptance is asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation

open Finset Real
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.ActualReserve.ActualReservePrimeMask
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
  (block mem_block first_margin positive_margin_mem)
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff (firstLayerPrice)

private theorem first_loss_zero_off_support {X : ℝ} (hX : 1 < X)
    (n : ℕ) {p : ℕ} (hp : p.Prime) (hnot : p ∉ lossPrimes X n) :
    layerLoss X n p 1 = 0 := by
  have hn : p ∉ n.primeFactors := fun h => hnot (mem_union_right _ h)
  have hv : n.factorization p = 0 := by
    by_contra h
    exact hn (by rwa [← Nat.support_factorization, Finsupp.mem_support_iff])
  have hg : rawLayerMargin X p 1 ≤ 0 :=
    le_of_not_gt (fun h => hnot (positive_margin_mem hX n hp h))
  simp [layerLoss, hv, max_eq_right hg]

private theorem first_loss_sum_on {X : ℝ} (hX : 1 < X) (n : ℕ)
    (S : Finset ℕ) (hsub : lossPrimes X n ⊆ S)
    (hprime : ∀ p ∈ S, p.Prime) :
    completeFirstLayerLoss X n = ∑ p ∈ S, layerLoss X n p 1 := by
  unfold completeFirstLayerLoss
  exact sum_subset hsub (fun p hp hn => first_loss_zero_off_support hX n (hprime p hp) hn)

private theorem prefix_layer_loss {X : ℝ} {n A p : ℕ}
    (hprefix : n.primeFactors = Nat.primesLE A) (hp : p.Prime) :
    layerLoss X n p 1 = max (rawLayerMargin X p 1) 0 -
      if p ≤ A then rawLayerMargin X p 1 else 0 := by
  have hf : p ∈ n.primeFactors ↔ 1 ≤ n.factorization p := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  have hv : 1 ≤ n.factorization p ↔ p ≤ A := by
    rw [← hf, hprefix, Nat.mem_primesLE, and_iff_left hp]
  simp only [layerLoss, hv]

/- The optimizer max-part cancels after BOTH complete sums have been extended
to the union of their original supports. No optimizer-only prime is dropped. -/
theorem ordered_prefix_difference {X : ℝ} (hX : 1 < X)
    {m k P Q : ℕ} (hmprefix : m.primeFactors = Nat.primesLE P)
    (hkprefix : k.primeFactors = Nat.primesLE Q) (hPQ : P ≤ Q) :
    completeFirstLayerLoss X k - completeFirstLayerLoss X m =
      -(∑ p ∈ block (P : ℝ) Q, rawLayerMargin X p 1) := by
  classical
  let S := lossPrimes X m ∪ lossPrimes X k
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime := by
    rcases mem_union.mp hp with hp | hp
    · rcases mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    · rcases mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hPQ' : (P : ℝ) ≤ Q := by exact_mod_cast hPQ
  have hWsub : block (P : ℝ) Q ⊆ S := by
    intro p hp
    obtain ⟨hpp, _, hpQ⟩ := (mem_block hP0 hPQ').mp hp
    have hpk : p ∈ k.primeFactors := by
      rw [hkprefix]
      exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpQ, hpp⟩
    exact mem_union_right _ (mem_union_right _ hpk)
  have hzero (p : ℕ) (hp : p ∈ S) (hpW : p ∉ block (P : ℝ) Q) :
      layerLoss X k p 1 - layerLoss X m p 1 = 0 := by
    have hpp := hprime p hp
    rw [prefix_layer_loss hkprefix hpp, prefix_layer_loss hmprefix hpp]
    by_cases hpP : p ≤ P
    · have hpQ : p ≤ Q := hpP.trans hPQ
      simp [hpP, hpQ]
    · have hpQ : ¬ p ≤ Q := by
        intro hpQ
        exact hpW ((mem_block hP0 hPQ').mpr
          ⟨hpp, by exact_mod_cast (Nat.lt_of_not_ge hpP), by exact_mod_cast hpQ⟩)
      simp [hpP, hpQ]
  have hterm (p : ℕ) (hp : p ∈ block (P : ℝ) Q) :
      layerLoss X k p 1 - layerLoss X m p 1 = -rawLayerMargin X p 1 := by
    obtain ⟨hpp, hPp, hpQ⟩ := (mem_block hP0 hPQ').mp hp
    have hpP : ¬ p ≤ P := not_le_of_gt (by exact_mod_cast hPp)
    have hpQ' : p ≤ Q := by exact_mod_cast hpQ
    rw [prefix_layer_loss hkprefix hpp, prefix_layer_loss hmprefix hpp,
      if_pos hpQ', if_neg hpP]
    ring
  rw [first_loss_sum_on hX k S subset_union_right hprime,
    first_loss_sum_on hX m S subset_union_left hprime, ← sum_sub_distrib]
  calc
    _ = ∑ p ∈ block (P : ℝ) Q, (layerLoss X k p 1 - layerLoss X m p 1) :=
      (sum_subset hWsub hzero).symm
    _ = ∑ p ∈ block (P : ℝ) Q, -rawLayerMargin X p 1 := sum_congr rfl hterm
    _ = _ := by rw [sum_neg_distrib]

private theorem raw_first_hasDerivAt {X t : ℝ} (hX : 4 < X) (ht : X / 2 ≤ t) :
    HasDerivAt (fun u : ℝ => log (1 + 1 / u) - log u / (X * log X))
      (-1 / (t * (t + 1)) - 1 / (X * log X * t)) t := by
  have hX0 : 0 < X := by linarith
  have ht0 : 0 < t := by linarith
  have hL : 0 < log X := log_pos (by linarith)
  have hi := (hasDerivAt_id t).inv ht0.ne'
  have hd := (((hasDerivAt_const t (1 : ℝ)).add hi).log
    (show 1 + t⁻¹ ≠ 0 by positivity)).sub
      ((Real.hasDerivAt_log ht0.ne').div_const (X * log X))
  convert hd using 1
  · ext u
    simp only [one_div, Pi.sub_apply, Pi.add_apply, Pi.inv_apply, id_eq]
  · simp only [Pi.add_apply, Pi.inv_apply, id_eq]
    field_simp [ht0.ne', hX0.ne', hL.ne',
      (show t + 1 ≠ 0 by positivity)]
    <;> ring

private theorem raw_first_derivative_bound {X t : ℝ} (hX : 4 < X)
    (ht : X / 2 ≤ t) :
    |-1 / (t * (t + 1)) - 1 / (X * log X * t)| ≤ 6 / X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have ht0 : 0 < t := by linarith
  have hL : 1 < log X := (Real.lt_log_iff_exp_lt hX0).mpr
    (Real.exp_one_lt_three.trans (by linarith))
  have hL0 : 0 < log X := by linarith
  have hsq : X ^ 2 ≤ 4 * t ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * t - X by linarith)
      (show 0 ≤ 2 * t + X by positivity)]
  have hfirst : 1 / (t * (t + 1)) ≤ 4 / X ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos ht0 (by linarith)) (sq_pos_of_pos hX0)).mpr
    nlinarith
  have hsecond : 1 / (X * log X * t) ≤ 2 / X ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < X * log X * t)
      (sq_pos_of_pos hX0)).mpr
    have hlt : t ≤ log X * t := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hL.le ht0.le
    have hmul := mul_le_mul_of_nonneg_left hlt hX0.le
    have hxt := mul_le_mul_of_nonneg_left ht hX0.le
    nlinarith
  have hnonpos : -1 / (t * (t + 1)) - 1 / (X * log X * t) ≤ 0 := by
    have ha : 0 ≤ 1 / (t * (t + 1)) := by positivity
    have hb : 0 ≤ 1 / (X * log X * t) := by positivity
    simp only [neg_div]
    linarith only [ha, hb]
  calc
    _ = 1 / (t * (t + 1)) + 1 / (X * log X * t) := by
      rw [abs_of_nonpos hnonpos]
      ring
    _ ≤ 4 / X ^ 2 + 2 / X ^ 2 := add_le_add hfirst hsecond
    _ = 6 / X ^ 2 := by ring

theorem raw_first_bound_at_root {X r t : ℝ} (hX : 4 < X)
    (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X)
    (ht : t ∈ Set.Icc (X / 2) (2 * X)) :
    |log (1 + 1 / t) - log t / (X * log X)| ≤ (6 / X ^ 2) * |t - r| := by
  have hr1 : 1 < r := by linarith [hr.1]
  have hroot0 : log (1 + 1 / r) - log r / (X * log X) = 0 := by
    have h := (div_eq_iff (log_pos hr1).ne').mp hroot
    change log (1 + 1 / r) = referencePrice X * log r at h
    rw [referencePrice] at h
    calc
      _ = log (1 + 1 / r) - (1 / (X * log X)) * log r := by ring
      _ = 0 := sub_eq_zero.mpr h
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u : ℝ => log (1 + 1 / u) - log u / (X * log X))
    (f' := fun u : ℝ => -1 / (u * (u + 1)) - 1 / (X * log X * u))
    (C := 6 / X ^ 2)
    (fun u hu => (raw_first_hasDerivAt hX hu.1).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using raw_first_derivative_bound hX hu.1)
    (convex_Icc (X / 2) (2 * X)) hr ht
  simpa only [Real.norm_eq_abs, hroot0, sub_zero] using hmv

private theorem ordered_prefix_bound {X r : ℝ} (hX : 4 < X)
    {m k P Q : ℕ} (hmprefix : m.primeFactors = Nat.primesLE P)
    (hkprefix : k.primeFactors = Nat.primesLE Q) (hPQ : P ≤ Q)
    (hP : (P : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X) :
    |completeFirstLayerLoss X k - completeFirstLayerLoss X m| ≤
      6 * max (|(P : ℝ) - r|) (|(Q : ℝ) - r|) *
        |Chebyshev.theta (P : ℝ) - Chebyshev.theta (Q : ℝ)| /
          (X ^ 2 * log (X / 2)) := by
  classical
  let W := block (P : ℝ) Q
  let M := max (|(P : ℝ) - r|) (|(Q : ℝ) - r|)
  have hX0 : 0 < X := by linarith
  have hL : 0 < log (X / 2) := log_pos (by linarith)
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hPQ' : (P : ℝ) ≤ Q := by exact_mod_cast hPQ
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hK : 0 ≤ (6 / X ^ 2) * M := mul_nonneg (by positivity) hM
  have htheta : (∑ p ∈ W, log (p : ℝ)) =
      Chebyshev.theta (Q : ℝ) - Chebyshev.theta (P : ℝ) := by
    have hsub : Nat.primesLE P ⊆ Nat.primesLE Q := Nat.primesLE_mono hPQ
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
    apply eq_sub_iff_add_eq.mpr
    simpa [W, block] using (sum_sdiff hsub (f := fun p : ℕ => log (p : ℝ)))
  have hcount : (W.card : ℝ) * log (X / 2) ≤
      Chebyshev.theta (Q : ℝ) - Chebyshev.theta (P : ℝ) := by
    rw [← htheta]
    calc
      _ = ∑ _p ∈ W, log (X / 2) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro p hp
        obtain ⟨_, hPp, _⟩ := (mem_block hP0 hPQ').mp hp
        exact log_le_log (by linarith) (hP.1.trans hPp.le)
  have hmass : 0 ≤ Chebyshev.theta (Q : ℝ) - Chebyshev.theta (P : ℝ) :=
    (mul_nonneg (Nat.cast_nonneg W.card) hL.le).trans hcount
  have hcard : (W.card : ℝ) ≤
      (Chebyshev.theta (Q : ℝ) - Chebyshev.theta (P : ℝ)) / log (X / 2) :=
    (le_div_iff₀ hL).mpr hcount
  have hterm (p : ℕ) (hp : p ∈ W) : |rawLayerMargin X p 1| ≤ (6 / X ^ 2) * M := by
    obtain ⟨hpp, hPp, hpQ⟩ := (mem_block hP0 hPQ').mp hp
    have hpTube : (p : ℝ) ∈ Set.Icc (X / 2) (2 * X) :=
      ⟨hP.1.trans hPp.le, hpQ.trans hQ.2⟩
    have hpM : |(p : ℝ) - r| ≤ M := by
      have hleft := (abs_le.mp (le_max_left (|(P : ℝ) - r|) (|(Q : ℝ) - r|))).1
      have hright := (abs_le.mp (le_max_right (|(P : ℝ) - r|) (|(Q : ℝ) - r|))).2
      apply abs_le.mpr
      dsimp [M] at *
      constructor <;> linarith
    rw [first_margin hpp]
    exact (raw_first_bound_at_root hX hr hroot hpTube).trans
      (mul_le_mul_of_nonneg_left hpM (by positivity))
  calc
    _ = |∑ p ∈ W, rawLayerMargin X p 1| := by
      rw [ordered_prefix_difference (by linarith) hmprefix hkprefix hPQ, abs_neg]
    _ ≤ ∑ p ∈ W, |rawLayerMargin X p 1| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ W, (6 / X ^ 2) * M := sum_le_sum hterm
    _ = (W.card : ℝ) * ((6 / X ^ 2) * M) := by simp
    _ ≤ ((Chebyshev.theta (Q : ℝ) - Chebyshev.theta (P : ℝ)) / log (X / 2)) *
        ((6 / X ^ 2) * M) := mul_le_mul_of_nonneg_right hcard hK
    _ = _ := by
      rw [abs_sub_comm (Chebyshev.theta (P : ℝ)) (Chebyshev.theta (Q : ℝ)),
        abs_of_nonneg hmass]
      dsimp [M]
      ring

/-- Finite cancellation for the COMPLETE union-support first-layer losses.
The endpoints are arbitrary natural prefix cutoffs, including equal cutoffs.
The root uses the existing real first-layer price. -/
theorem complete_first_layer_prefix_cancellation {X r : ℝ} (hX : 4 < X)
    {m k P Q : ℕ}
    (hmprefix : m.primeFactors = Nat.primesLE P)
    (hkprefix : k.primeFactors = Nat.primesLE Q)
    (hP : (P : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X) :
    |completeFirstLayerLoss X k - completeFirstLayerLoss X m| ≤
      6 * max (|(P : ℝ) - r|) (|(Q : ℝ) - r|) *
        |Chebyshev.theta (P : ℝ) - Chebyshev.theta (Q : ℝ)| /
          (X ^ 2 * log (X / 2)) := by
  rcases le_total P Q with hPQ | hQP
  · exact ordered_prefix_bound hX hmprefix hkprefix hPQ hP hQ hr hroot
  · have h := ordered_prefix_bound hX hkprefix hmprefix hQP hQ hP hr hroot
    rw [abs_sub_comm (completeFirstLayerLoss X m) (completeFirstLayerLoss X k),
      max_comm (|(Q : ℝ) - r|) (|(P : ℝ) - r|),
      abs_sub_comm (Chebyshev.theta (Q : ℝ)) (Chebyshev.theta (P : ℝ))] at h
    exact h

theorem defect_eq_first_of_optimizer_higher_layers {X : ℝ}
    (hX : 1 < X) {k : ℕ} (hk : 1 ≤ k)
    (hhigher : ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →
      (j ≤ k.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p)) :
    actualDefect X k = completeFirstLayerLoss X k := by
  have hzero (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : 2 ≤ j) :
      layerLoss X k p j = 0 := by
    have hact := margin_active_iff hX hp (by omega : 1 ≤ j)
    by_cases hc : j ≤ optimalLayerCount (referencePrice X) p
    · have hg : 0 ≤ rawLayerMargin X p j := (hact.mpr hc).le
      simp [layerLoss, (hhigher p hp j hj).mpr hc, max_eq_left hg]
    · have hg : rawLayerMargin X p j ≤ 0 := le_of_not_gt (fun h => hc (hact.mp h))
      have hk' : ¬ j ≤ k.factorization p := fun h => hc ((hhigher p hp j hj).mp h)
      simp [layerLoss, hk', max_eq_right hg]
  have hprime (p : ℕ) (hp : p ∈ lossPrimes X k) : p.Prime := by
    rcases mem_union.mp hp with hp | hp <;> exact Nat.prime_of_mem_primeFactors hp
  have htwo : completeSecondLayerLoss X k = 0 := by
    apply sum_eq_zero
    intro p hp
    exact hzero p (hprime p hp) 2 le_rfl
  have hhigh : completeHigherLayerLoss X k = 0 := by
    apply sum_eq_zero
    intro p hp
    apply sum_eq_zero
    intro j hj
    exact hzero p (hprime p hp) j (by have := (mem_Icc.mp hj).1; omega)
  have hs := actual_defect_decomposition hX hk
  rw [htwo, hhigh, add_zero, add_zero] at hs
  exact hs

/- The original record price mu remains arbitrary. A budget equality supplies
k<=m; equality k=m uses reflexivity, so no predecessor premise is misapplied. -/
private theorem record_budget_comparison {X δ mu : ℝ} {m k : ℕ}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hmu : 0 < mu)
    (hrecord : ∀ a : ℕ, 0 < a → a < m →
      goldenResourceObjective mu a < goldenResourceObjective mu m)
    (hclock : X = log (m : ℝ)) (hδ : 0 ≤ δ)
    (hbudget : log (k : ℝ) + δ = X) :
    actualDefect X m ≤ actualDefect X k + δ / (X * log X) := by
  have hlogs : log (m : ℝ) = log (k : ℝ) + δ := by linarith
  have hkm : k ≤ m := by
    by_contra hn
    have hmk : m < k := by omega
    have hl := log_lt_log (show (0 : ℝ) < m by exact_mod_cast (show 0 < m by omega))
      (show (m : ℝ) < k by exact_mod_cast hmk)
    linarith
  have hobj : goldenResourceObjective mu k ≤ goldenResourceObjective mu m := by
    rcases lt_or_eq_of_le hkm with hlt | heq
    · exact (hrecord k (by omega) hlt).le
    · subst k
      exact le_rfl
  unfold actualDefect goldenResourceObjective
  unfold goldenResourceObjective at hobj
  rw [hlogs] at hobj ⊢
  have hμδ : 0 ≤ mu * δ := mul_nonneg hmu.le hδ
  have heq : δ / (X * log X) = referencePrice X * δ := by
    unfold referencePrice
    ring
  rw [heq]
  nlinarith

/-- A budget candidate with exactly the canonical higher occupancies controls
the ORIGINAL arbitrary-positive-price record's entire nonfirst loss.
The candidate is not assumed to be a record or an optimizer. -/
theorem actual_record_prefix_budget_residual {X r δ mu : ℝ} {m k P Q : ℕ}
    (hX : 4 < X) (hm : 2 ≤ m) (hk : 2 ≤ k) (hmu : 0 < mu)
    (hrecord : ∀ a : ℕ, 0 < a → a < m →
      goldenResourceObjective mu a < goldenResourceObjective mu m)
    (hclock : X = log (m : ℝ))
    (hmprefix : m.primeFactors = Nat.primesLE P)
    (hkprefix : k.primeFactors = Nat.primesLE Q)
    (hP : (P : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X))
    (hr : r ∈ Set.Icc (X / 2) (2 * X))
    (hroot : firstLayerPrice r = referencePrice X)
    (hδ : 0 ≤ δ) (hbudget : log (k : ℝ) + δ = X)
    (hhigher : ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →
      (j ≤ k.factorization p ↔ j ≤ optimalLayerCount (referencePrice X) p)) :
    0 ≤ actualDefect X m - completeFirstLayerLoss X m ∧
    actualDefect X m - completeFirstLayerLoss X m ≤
      6 * max (|(P : ℝ) - r|) (|(Q : ℝ) - r|) *
        |Chebyshev.theta (P : ℝ) - Chebyshev.theta (Q : ℝ)| /
          (X ^ 2 * log (X / 2)) + δ / (X * log X) := by
  have hX1 : 1 < X := by linarith
  have hsplit := actual_defect_decomposition hX1 (show 1 ≤ m by omega)
  have htwo : 0 ≤ completeSecondLayerLoss X m :=
    sum_nonneg (fun p _ => layer_loss_nonneg X m p 2)
  have hhigh : 0 ≤ completeHigherLayerLoss X m :=
    sum_nonneg (fun p _ => sum_nonneg (fun j _ => layer_loss_nonneg X m p j))
  have hcandidate := defect_eq_first_of_optimizer_higher_layers hX1
    (show 1 ≤ k by omega) hhigher
  have hcompare := record_budget_comparison (show 1 ≤ m by omega)
    (show 1 ≤ k by omega) hmu hrecord hclock hδ hbudget
  rw [hcandidate] at hcompare
  have hcancel := complete_first_layer_prefix_cancellation hX hmprefix hkprefix
    hP hQ hr hroot
  have habs := le_abs_self (completeFirstLayerLoss X k - completeFirstLayerLoss X m)
  constructor <;> linarith

#print axioms complete_first_layer_prefix_cancellation
#print axioms actual_record_prefix_budget_residual

end D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
