/- GID: D5/S3/Estimation/Fano
   generality: G
   mirror-B: D5/B/S3/Estimation/Fano
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound finite conditional entropy by estimator error in nats. -/

/- Library-search audit trail (2026-08-11):
   * Local pinned-mathlib grep terms covered `Fano`/`fano`, finite/Shannon/conditional entropy,
     entropy versus finite cardinality, binary entropy, concavity/Jensen, and finite log-sum.
     No Fano inequality or finite Shannon-entropy functional was found. Mathlib does provide
     the nats-valued scalar `Real.binEntropy` and general convexity machinery.
   * Every declaration under `D5/S3` was scanned (708 declarations), followed by rearranged
     searches for Fano, conditional/Shannon entropy, mutual information, entropy under maps,
     and binary entropy. There is no Fano declaration. The useful existing shortening is
     `DivergenceSupport.LogSumInequality.log_sum_inequality`.
   * `Quantum.CloningMachine.binaryEntropyBits` was found as the repository's only declared
     binary entropy. It uses `Real.logb 2` and is measured in bits, so using it with the nats-valued
     `shannonEntropy` would corrupt Fano's constant. The bound therefore writes the binary term
     directly as `shannonEntropy (fun b : Bool => if b then e else 1 - e)`.
-/

import D5.S3.DivergenceSupport.LogSumInequality
import D5.S3.Entropy.ConditionalEntropy

/-!
# Weak finite Fano inequality

For `p : Y × X → ℝ`, the first coordinate `Y` is the observation and the second coordinate
`X` is the estimand. Thus the repository convention makes `conditionalEntropy p` exactly
`H(X | Y)`. The theorem below proves the weak finite Fano bound

`H(X | Y) ≤ h(e) + e * log (card X)`,

where `e` is the mass of `{(y, x) | g y ≠ x}` and `h(e)` is written as the Shannon entropy
of its `Bool` law, in nats. The stronger `log (card X - 1)` refinement is intentionally not
claimed here: it requires separating the singleton estimand case, where Lean totalizes
`Real.log 0` to `0`.

The result covers all finite observation and estimand types carrying a nonnegative normalized
joint law, including `e = 0`, `e = 1`, zero-marginal observation slices, and singleton types.
It does not claim a probability bound for signed or unnormalized weights.
-/

namespace D5.S3.Estimation.Fano

open D5.S3.Divergence.ChainRule
open D5.S3.DivergenceSupport.LogSumInequality
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.MaxEntropy

open Classical in
/-- Weak finite Fano inequality in nats for an arbitrary estimator. -/
theorem fano_inequality_weak {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1) :
    let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
    conditionalEntropy p ≤
      shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log (Fintype.card X) := by
  classical
  let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
  change conditionalEntropy p ≤
    shannonEntropy (fun b : Bool => if b then e else 1 - e) +
      e * Real.log (Fintype.card X)
  have hsum_ne : ∑ z, p z ≠ 0 := by
    rw [hp.2]
    norm_num
  obtain ⟨z₀, _, hz₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  letI : Nonempty Y := ⟨z₀.1⟩
  letI : Nonempty X := ⟨z₀.2⟩
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
      (∑ z : Y × X, marginal p z.1) = (Fintype.card X : ℝ) := by
    simp only [Fintype.sum_prod_type]
    calc
      (∑ y, ∑ _x : X, marginal p y) =
          ∑ y, (Fintype.card X : ℝ) * marginal p y := by simp
      _ = (Fintype.card X : ℝ) * ∑ y, marginal p y := by
            rw [Finset.mul_sum]
      _ = (Fintype.card X : ℝ) := by rw [hm_sum, mul_one]
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
    (fun z : Y × X => marginal p z.1)
    (fun z => by
      by_cases hz : g z.1 ≠ z.2 <;> simp [hz, hp.1 z])
    (fun z => hm_nonneg z.1)
    (fun z hz0 => by
      have hpz : p z = 0 := hp_zero_of_marginal_zero z.1 z.2 hz0
      simp [hpz])
  have herror_log :
      e * Real.log (e / (Fintype.card X : ℝ)) ≤
        ∑ z, if g z.1 ≠ z.2 then
          p z * Real.log (p z / marginal p z.1) else 0 := by
    calc
      e * Real.log (e / (Fintype.card X : ℝ)) =
          (∑ z, if g z.1 ≠ z.2 then p z else 0) *
            Real.log
              ((∑ z, if g z.1 ≠ z.2 then p z else 0) /
                (∑ z : Y × X, marginal p z.1)) := by
                  rw [show e = ∑ z, if g z.1 ≠ z.2 then p z else 0 by rfl,
                    herror_reference]
      _ ≤ ∑ z, (if g z.1 ≠ z.2 then p z else 0) *
          Real.log
            ((if g z.1 ≠ z.2 then p z else 0) / marginal p z.1) := herror_log_raw
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
          e * Real.log (e / (Fintype.card X : ℝ)) ≤
        ∑ z, p z * Real.log (p z / marginal p z.1) := by
    calc
      (1 - e) * Real.log (1 - e) +
          e * Real.log (e / (Fintype.card X : ℝ)) ≤
        (∑ z, if g z.1 = z.2 then
            p z * Real.log (p z / marginal p z.1) else 0) +
          (∑ z, if g z.1 ≠ z.2 then
            p z * Real.log (p z / marginal p z.1) else 0) :=
              add_le_add hcorrect_log herror_log
      _ = ∑ z, p z * Real.log (p z / marginal p z.1) := hratio_split
  have hcard_ne : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hfinal_identity :
      -((1 - e) * Real.log (1 - e) +
          e * Real.log (e / (Fintype.card X : ℝ))) =
        shannonEntropy (fun b : Bool => if b then e else 1 - e) +
          e * Real.log (Fintype.card X) := by
    by_cases he : e = 0
    · simp [he, shannonEntropy]
    · rw [Real.log_div he hcard_ne]
      simp only [shannonEntropy, Fintype.sum_bool, Real.negMulLog]
      simp
      ring
  rw [hentropy_identity]
  calc
    -(∑ z, p z * Real.log (p z / marginal p z.1)) ≤
        -((1 - e) * Real.log (1 - e) +
          e * Real.log (e / (Fintype.card X : ℝ))) := neg_le_neg hlog
    _ = shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log (Fintype.card X) := hfinal_identity

/- On singleton observation and estimand types, the error and both entropy terms are zero.
The cardinality-minus-one logarithm from strong Fano is totalized to `Real.log 0 = 0`. -/
example :
    let p : Unit × Unit → ℝ := fun _ => 1
    let g : Unit → Unit := fun _ => ()
    let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
    e = 0 ∧ conditionalEntropy p = 0 ∧
      shannonEntropy (fun b : Bool => if b then e else 1 - e) = 0 ∧
        Real.log ((Fintype.card Unit - 1 : ℕ) : ℝ) = 0 := by
  norm_num [conditionalEntropy, marginal, conditional, shannonEntropy]

/- For an unobserved uniform bit and a constant estimator, weak Fano is strict. -/
example :
    let p : Unit × Bool → ℝ := fun _ => 1 / 2
    let g : Unit → Bool := fun _ => false
    let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
    conditionalEntropy p <
      shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log (Fintype.card Bool) := by
  dsimp
  simp only [conditionalEntropy, marginal, conditional, shannonEntropy,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [Real.negMulLog]
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

open Classical in
/- Neither reflexivity nor simplification proves the estimator-independent bound. -/
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1) :
    let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
    conditionalEntropy p ≤
      shannonEntropy (fun b : Bool => if b then e else 1 - e) +
        e * Real.log (Fintype.card X) := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact fano_inequality_weak p g hp

#print axioms fano_inequality_weak

end D5.S3.Estimation.Fano
