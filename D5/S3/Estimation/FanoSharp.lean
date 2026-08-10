/- GID: D5/S3/Estimation/FanoSharp
   generality: G
   mirror-B: D5/B/S3/Estimation/FanoSharp
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sharpen finite Fano's inequality to the off-estimator cardinality in nats. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep covered `Fano`/`fano`, finite/Shannon/conditional entropy,
     entropy against finite cardinality, binary entropy, and finite log-sum. The only `Fano`
     hit is the unrelated Fano plane; there is no Fano inequality. Mathlib's scalar
     `Real.binEntropy` does not supply a finite Fano theorem.
   * A declaration-pattern scan covered all 845 declarations under `D5/S3`, followed by
     rearranged searches for Fano, conditional/Shannon entropy, binary entropy, cardinality
     entropy bounds, and log-sum. The only Fano theorem is the frozen weak form in `Fano.lean`;
     the reusable engine is `DivergenceSupport.LogSumInequality.log_sum_inequality`.
   * `Quantum.CloningMachine.binaryEntropyBits` is the repository's only declared binary entropy.
     It uses `Real.logb 2` and is measured in bits, whereas every entropy here is in nats, so it
     is not used; the binary term remains the two-point `shannonEntropy` expression itself.
-/

import D5.S3.Estimation.Fano

/-!
# Sharp finite Fano inequality

For `p : Y × X → ℝ`, `Y` is the observation and `X` the estimand, so the frozen
`conditionalEntropy` is `H(X | Y)`. This file sharpens the weak theorem's error term from
`e * log (card X)` to `e * log (card X - 1)` by using only the off-estimator points as the
error reference measure.

The hypothesis `Fintype.card X ≠ 1` excludes exactly the diagnosed singleton obstruction.
At `card X = 1` the sharp logarithm is `Real.log 0`, totalized by Lean to zero; the compiled
witness below records that evaluation, but the theorem does not use totalization as a proof of
the singleton case. Normalization already forces `X` and `Y` to be nonempty, so no further
hypothesis beyond the weak theorem's nonnegative normalized joint law is added.
-/

namespace D5.S3.Estimation.FanoSharp

open D5.S3.Divergence.ChainRule
open D5.S3.DivergenceSupport.LogSumInequality
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy

open Classical in
/-- Sharp finite Fano inequality in nats. The `card X ≠ 1` hypothesis excludes the case in
which the displayed logarithm is the totalized value `Real.log 0`. -/
theorem fano_inequality_sharp {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : Fintype.card X ≠ 1) :
    let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
    conditionalEntropy p ≤
      shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log ((Fintype.card X : ℝ) - 1) := by
  classical
  let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
  change conditionalEntropy p ≤
    shannonEntropy (fun b : Bool => if b then e else 1 - e) +
      e * Real.log ((Fintype.card X : ℝ) - 1)
  have hsum_ne : ∑ z, p z ≠ 0 := by
    rw [hp.2]
    norm_num
  obtain ⟨z₀, _, hz₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  letI : Nonempty Y := ⟨z₀.1⟩
  letI : Nonempty X := ⟨z₀.2⟩
  have hcard_gt_one : 1 < Fintype.card X := by
    have hcard_pos : 0 < Fintype.card X := Fintype.card_pos
    omega
  have hm_nonneg (y : Y) : 0 ≤ marginal p y := by
    rw [marginal]
    exact Finset.sum_nonneg fun x _ => hp.1 (y, x)
  have hp_le_marginal (y : Y) (x : X) : p (y, x) ≤ marginal p y := by
    rw [marginal]
    exact Finset.single_le_sum
      (fun x' _ => hp.1 (y, x')) (Finset.mem_univ x)
  have hp_zero_of_marginal_zero (y : Y) (x : X) (hy : marginal p y = 0) :
      p (y, x) = 0 := by
    apply le_antisymm
    · exact (hp_le_marginal y x).trans_eq hy
    · exact hp.1 (y, x)
  have hm_sum : ∑ y, marginal p y = 1 := by
    simp only [marginal]
    rw [← Fintype.sum_prod_type]
    exact hp.2
  have hentropy_cell (y : Y) (x : X) :
      marginal p y * Real.negMulLog (conditional p y x) =
        -(p (y, x) * Real.log (p (y, x) / marginal p y)) := by
    by_cases hy : marginal p y = 0
    · have hyx := hp_zero_of_marginal_zero y x hy
      simp [conditional, hy, hyx]
    · rw [conditional]
      simp only [Real.negMulLog]
      field_simp [hy]
  have hentropy_identity :
      conditionalEntropy p =
        -(∑ z, p z * Real.log (p z / marginal p z.1)) := by
    rw [conditionalEntropy]
    simp only [shannonEntropy, Finset.mul_sum]
    calc
      (∑ y, ∑ x, marginal p y * Real.negMulLog (conditional p y x)) =
          ∑ y, ∑ x, -(p (y, x) * Real.log (p (y, x) / marginal p y)) := by
            exact Finset.sum_congr rfl fun y _ =>
              Finset.sum_congr rfl fun x _ => hentropy_cell y x
      _ = -(∑ y, ∑ x, p (y, x) * Real.log (p (y, x) / marginal p y)) := by
            simp_rw [Finset.sum_neg_distrib]
      _ = -(∑ z, p z * Real.log (p z / marginal p z.1)) := by
            rw [Fintype.sum_prod_type]
  have hmass_split :
      (∑ z, if g z.1 = z.2 then p z else 0) + e = 1 := by
    rw [show e = ∑ z, if g z.1 ≠ z.2 then p z else 0 by rfl]
    rw [← Finset.sum_add_distrib, ← hp.2]
    exact Finset.sum_congr rfl fun z _ => by
      by_cases hz : g z.1 = z.2 <;> simp [hz]
  have hcorrect_mass :
      (∑ z, if g z.1 = z.2 then p z else 0) = 1 - e := by
    linarith [hmass_split]
  have hcorrect_reference :
      (∑ z : Y × X, if g z.1 = z.2 then marginal p z.1 else 0) = 1 := by
    simp only [Fintype.sum_prod_type]
    calc
      (∑ y, ∑ x, if g y = x then marginal p y else 0) =
          ∑ y, marginal p y := by
            exact Finset.sum_congr rfl fun y _ => by simp
      _ = 1 := hm_sum
  have herror_reference :
      (∑ z : Y × X, if g z.1 ≠ z.2 then marginal p z.1 else 0) =
        (Fintype.card X : ℝ) - 1 := by
    simp only [Fintype.sum_prod_type]
    calc
      (∑ y, ∑ x, if g y ≠ x then marginal p y else 0) =
          ∑ y, ((Fintype.card X : ℝ) - 1) * marginal p y := by
            exact Finset.sum_congr rfl fun y _ => by
              calc
                (∑ x, if g y ≠ x then marginal p y else 0) =
                    ∑ x ∈ Finset.univ.erase (g y), marginal p y := by
                      rw [← Finset.sum_filter, Finset.filter_ne]
                _ = ((Fintype.card X : ℝ) - 1) * marginal p y := by
                      rw [Finset.sum_const, nsmul_eq_mul,
                        Finset.cast_card_erase_of_mem (Finset.mem_univ (g y)),
                        Finset.card_univ]
      _ = ((Fintype.card X : ℝ) - 1) * ∑ y, marginal p y := by
            rw [Finset.mul_sum]
      _ = (Fintype.card X : ℝ) - 1 := by rw [hm_sum, mul_one]
  have hcorrect_log_raw := log_sum_inequality
    (fun z : Y × X => if g z.1 = z.2 then p z else 0)
    (fun z : Y × X => if g z.1 = z.2 then marginal p z.1 else 0)
    (fun z => by
      by_cases hz : g z.1 = z.2 <;> simp [hz, hp.1 z])
    (fun z => by
      by_cases hz : g z.1 = z.2 <;> simp [hz, hm_nonneg z.1])
    (fun z hz0 => by
      by_cases hz : g z.1 = z.2
      · simp only [hz, if_true] at hz0 ⊢
        exact hp_zero_of_marginal_zero z.1 z.2 hz0
      · simp [hz])
  have hcorrect_log :
      (1 - e) * Real.log (1 - e) ≤
        ∑ z, if g z.1 = z.2 then
          p z * Real.log (p z / marginal p z.1) else 0 := by
    calc
      (1 - e) * Real.log (1 - e) =
          (∑ z, if g z.1 = z.2 then p z else 0) *
            Real.log
              ((∑ z, if g z.1 = z.2 then p z else 0) /
                (∑ z : Y × X, if g z.1 = z.2 then marginal p z.1 else 0)) := by
                  rw [hcorrect_mass, hcorrect_reference, div_one]
      _ ≤ ∑ z, (if g z.1 = z.2 then p z else 0) *
          Real.log
            ((if g z.1 = z.2 then p z else 0) /
              (if g z.1 = z.2 then marginal p z.1 else 0)) := hcorrect_log_raw
      _ = ∑ z, if g z.1 = z.2 then
          p z * Real.log (p z / marginal p z.1) else 0 := by
            exact Finset.sum_congr rfl fun z _ => by
              by_cases hz : g z.1 = z.2 <;> simp [hz]
  have herror_log_raw := log_sum_inequality
    (fun z : Y × X => if g z.1 ≠ z.2 then p z else 0)
    (fun z : Y × X => if g z.1 ≠ z.2 then marginal p z.1 else 0)
    (fun z => by
      by_cases hz : g z.1 ≠ z.2 <;> simp [hz, hp.1 z])
    (fun z => by
      by_cases hz : g z.1 ≠ z.2 <;> simp [hz, hm_nonneg z.1])
    (fun z hz0 => by
      by_cases hz : g z.1 ≠ z.2
      · rw [if_pos hz] at hz0 ⊢
        exact hp_zero_of_marginal_zero z.1 z.2 hz0
      · rw [if_neg hz])
  have herror_log :
      e * Real.log (e / ((Fintype.card X : ℝ) - 1)) ≤
        ∑ z, if g z.1 ≠ z.2 then
          p z * Real.log (p z / marginal p z.1) else 0 := by
    calc
      e * Real.log (e / ((Fintype.card X : ℝ) - 1)) =
          (∑ z, if g z.1 ≠ z.2 then p z else 0) *
            Real.log
              ((∑ z, if g z.1 ≠ z.2 then p z else 0) /
                (∑ z : Y × X,
                  if g z.1 ≠ z.2 then marginal p z.1 else 0)) := by
                    rw [show e = ∑ z, if g z.1 ≠ z.2 then p z else 0 by rfl,
                      herror_reference]
      _ ≤ ∑ z, (if g z.1 ≠ z.2 then p z else 0) *
          Real.log
            ((if g z.1 ≠ z.2 then p z else 0) /
              (if g z.1 ≠ z.2 then marginal p z.1 else 0)) := herror_log_raw
      _ = ∑ z, if g z.1 ≠ z.2 then
          p z * Real.log (p z / marginal p z.1) else 0 := by
            exact Finset.sum_congr rfl fun z _ => by
              by_cases hz : g z.1 ≠ z.2 <;> simp [hz]
  have hratio_split :
      (∑ z, if g z.1 = z.2 then
          p z * Real.log (p z / marginal p z.1) else 0) +
        (∑ z, if g z.1 ≠ z.2 then
          p z * Real.log (p z / marginal p z.1) else 0) =
        ∑ z, p z * Real.log (p z / marginal p z.1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by
      by_cases hz : g z.1 = z.2 <;> simp [hz]
  have hlog :
      (1 - e) * Real.log (1 - e) +
          e * Real.log (e / ((Fintype.card X : ℝ) - 1)) ≤
        ∑ z, p z * Real.log (p z / marginal p z.1) := by
    calc
      (1 - e) * Real.log (1 - e) +
          e * Real.log (e / ((Fintype.card X : ℝ) - 1)) ≤
        (∑ z, if g z.1 = z.2 then
            p z * Real.log (p z / marginal p z.1) else 0) +
          (∑ z, if g z.1 ≠ z.2 then
            p z * Real.log (p z / marginal p z.1) else 0) :=
              add_le_add hcorrect_log herror_log
      _ = ∑ z, p z * Real.log (p z / marginal p z.1) := hratio_split
  have hcard_real_gt_one : (1 : ℝ) < Fintype.card X := by
    exact_mod_cast hcard_gt_one
  have hcard_sub_ne : (Fintype.card X : ℝ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hcard_real_gt_one)
  have hfinal_identity :
      -((1 - e) * Real.log (1 - e) +
          e * Real.log (e / ((Fintype.card X : ℝ) - 1))) =
        shannonEntropy (fun b : Bool => if b then e else 1 - e) +
          e * Real.log ((Fintype.card X : ℝ) - 1) := by
    by_cases he : e = 0
    · simp [he, shannonEntropy]
    · rw [Real.log_div he hcard_sub_ne]
      simp only [shannonEntropy, Fintype.sum_bool, Real.negMulLog]
      simp
      ring
  rw [hentropy_identity]
  calc
    -(∑ z, p z * Real.log (p z / marginal p z.1)) ≤
        -((1 - e) * Real.log (1 - e) +
          e * Real.log (e / ((Fintype.card X : ℝ) - 1))) := neg_le_neg hlog
    _ = shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log ((Fintype.card X : ℝ) - 1) := hfinal_identity

/-- On `card X > 1` and for nonnegative error mass, the sharp right-hand side is no larger
than the right-hand side of the frozen `Fano.fano_inequality_weak`. Thus the sharp bound implies
the weak bound throughout their common range. -/
theorem fano_sharp_rhs_le_weak_rhs {X : Type*} [Fintype X]
    (e : ℝ) (he : 0 ≤ e) (hX : 1 < Fintype.card X) :
    shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log ((Fintype.card X : ℝ) - 1) ≤
      shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log (Fintype.card X) := by
  have hcard_real_gt_one : (1 : ℝ) < Fintype.card X := by
    exact_mod_cast hX
  have hlog :
      Real.log ((Fintype.card X : ℝ) - 1) ≤ Real.log (Fintype.card X) :=
    Real.log_le_log (sub_pos.mpr hcard_real_gt_one) (by linarith)
  simpa only [add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_left hlog he)
      (shannonEntropy (fun b : Bool => if b then e else 1 - e))

/- At `card X = 1`, the actual singleton sharp right-hand side is zero: in particular its
logarithm is the totalized `Real.log 0 = 0`. This documents, but does not prove away, the excluded
case. -/
example :
    let p : Unit × Unit → ℝ := fun _ => 1
    let g : Unit → Unit := fun _ => ()
    let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
    shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log ((Fintype.card Unit : ℝ) - 1) = 0 := by
  norm_num [shannonEntropy, Real.negMulLog]

/- For an unobserved uniform bit and a constant estimator, the sharp right-hand side is strictly
smaller than the weak right-hand side: `e = 1/2`, `log (card Bool - 1) = 0`, and `log 2 > 0`. -/
example :
    let p : Unit × Bool → ℝ := fun _ => 1 / 2
    let g : Unit → Bool := fun _ => false
    let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
    shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log ((Fintype.card Bool : ℝ) - 1) <
      shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log (Fintype.card Bool) := by
  dsimp
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, shannonEntropy]
  norm_num [Real.negMulLog]
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

open Classical in
/- Neither reflexivity nor simplification proves the sharp estimator-independent bound. -/
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : Fintype.card X ≠ 1) :
    let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
    conditionalEntropy p ≤
      shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log ((Fintype.card X : ℝ) - 1) := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact fano_inequality_sharp p g hp hX

#print axioms fano_inequality_sharp
#print axioms fano_sharp_rhs_le_weak_rhs

end D5.S3.Estimation.FanoSharp
