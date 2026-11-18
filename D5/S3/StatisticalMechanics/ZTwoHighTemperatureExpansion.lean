/- GID: D5/S3/StatisticalMechanics/ZTwoHighTemperatureExpansion
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/ZTwoHighTemperatureExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity sums of plaquette products over 𝔽₂ keep the plaquette sets with given boundary. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming

/-! # The high-temperature expansion over `𝔽₂`

Let `E` and `P` be finite types and let `M : Matrix P E (ZMod 2)` be an incidence matrix over
`𝔽₂`. For a configuration `σ : E → ZMod 2` the value `(M *ᵥ σ) p` is the parity of `σ` along
the row `p`. Write `sgn 0 = 1` and `sgn 1 = -1` in a commutative ring `R`. For every `t : R`
and every `c : E → ZMod 2`,

`∑ σ, sgn (c ⬝ᵥ σ) * ∏ p, (1 + t * sgn ((M *ᵥ σ) p))
  = 2 ^ |E| * ∑ S with Mᵀ *ᵥ S = c, t ^ (hammingNorm S)`.

Expanding the product over the rows gives a sum over `S : P → ZMod 2` of
`t ^ (hammingNorm S) * sgn (S ⬝ᵥ M *ᵥ σ)`, and `S ⬝ᵥ M *ᵥ σ = (Mᵀ *ᵥ S) ⬝ᵥ σ`. The sum of
`sgn (v ⬝ᵥ σ)` over all `σ` factors coordinatewise into `∏ e, (1 + sgn (v e))`, which is
`2 ^ |E|` when `v = 0` and `0` otherwise; applied to `v = c + Mᵀ *ᵥ S` this keeps exactly the
`S` with `Mᵀ *ᵥ S = c`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix

namespace D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion

/-- The sign of an element of `𝔽₂` in a ring: `sgn 0 = 1` and `sgn 1 = -1`. -/
def sgn (R : Type*) [Ring R] (z : ZMod 2) : R := if z = 0 then 1 else -1

section

variable {R : Type*} [CommRing R]

private theorem univ_zmod_two : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem sgn_zero : sgn R 0 = 1 := by
  simp [sgn]

private theorem sgn_add (a b : ZMod 2) : sgn R (a + b) = sgn R a * sgn R b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [sgn, h11]

private theorem sgn_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn R (∑ i ∈ s, f i) = ∏ i ∈ s, sgn R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, sgn_add, ih]

/-- Summing over one coordinate: `∑ b, sgn (a * b)` is `2` when `a = 0` and `0` otherwise. -/
private theorem sum_sgn_mul (a : ZMod 2) :
    ∑ b : ZMod 2, sgn R (a * b) = if a = 0 then 2 else 0 := by
  rw [univ_zmod_two, Finset.sum_pair zero_ne_one]
  rcases zmod_two_cases a with rfl | rfl <;> simp [sgn, one_add_one_eq_two]

/-- Orthogonality of the parity characters on `E → ZMod 2`. -/
private theorem sum_sgn_dotProduct {E : Type*} [Fintype E] [DecidableEq E] (v : E → ZMod 2) :
    ∑ σ : E → ZMod 2, sgn R (v ⬝ᵥ σ) = if v = 0 then 2 ^ Fintype.card E else 0 := by
  have h : ∀ σ : E → ZMod 2, sgn R (v ⬝ᵥ σ) = ∏ e, sgn R (v e * σ e) := fun σ => by
    rw [dotProduct, sgn_sum]
  simp_rw [h]
  rw [← Fintype.prod_sum (fun e b => sgn R (v e * b))]
  simp_rw [sum_sgn_mul]
  split_ifs with hv
  · simp [hv]
  · obtain ⟨e, he⟩ : ∃ e, v e ≠ 0 := by
      by_contra hc
      exact hv (funext fun e => not_not.mp fun h' => hc ⟨e, h'⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

/-- Expansion of the plaquette product over the plaquette sets `S`. -/
private theorem prod_one_add_eq_sum {P : Type*} [Fintype P] [DecidableEq P] (t : R)
    (x : P → ZMod 2) :
    ∏ p, (1 + t * sgn R (x p)) =
      ∑ S : P → ZMod 2, t ^ hammingNorm S * sgn R (S ⬝ᵥ x) := by
  have hp : ∀ p, 1 + t * sgn R (x p) =
      ∑ b : ZMod 2, (if b = 0 then 1 else t) * sgn R (b * x p) := by
    intro p
    rw [univ_zmod_two, Finset.sum_pair zero_ne_one]
    simp [sgn]
  simp_rw [hp]
  rw [Fintype.prod_sum (fun p b => (if b = 0 then 1 else t) * sgn R (b * x p))]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib, dotProduct, sgn_sum]
  congr 1
  rw [hammingNorm, ← Finset.prod_const, Finset.prod_filter]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hS : S p = 0 <;> simp [hS]

/-- The high-temperature expansion over `𝔽₂`: for an incidence matrix `M : Matrix P E (ZMod 2)`,
a loop `c : E → ZMod 2` and `t` in a commutative ring, the parity-weighted sum of the plaquette
products over all configurations `σ : E → ZMod 2` equals `2 ^ |E|` times the sum of
`t ^ (hammingNorm S)` over the plaquette sets `S : P → ZMod 2` with boundary `Mᵀ *ᵥ S = c`. -/
theorem sum_sgn_mul_prod_one_add_eq {E P : Type*} [Fintype E] [DecidableEq E] [Fintype P]
    [DecidableEq P] (M : Matrix P E (ZMod 2)) (t : R) (c : E → ZMod 2) :
    ∑ σ : E → ZMod 2, sgn R (c ⬝ᵥ σ) * ∏ p, (1 + t * sgn R ((M *ᵥ σ) p)) =
      2 ^ Fintype.card E *
        ∑ S ∈ Finset.univ.filter (fun S : P → ZMod 2 => Mᵀ *ᵥ S = c), t ^ hammingNorm S := by
  have hc : ∀ S : P → ZMod 2, c + Mᵀ *ᵥ S = 0 ↔ Mᵀ *ᵥ S = c := fun S => by
    rw [add_eq_zero_iff_eq_neg', ZModModule.neg_eq_self]
  calc ∑ σ : E → ZMod 2, sgn R (c ⬝ᵥ σ) * ∏ p, (1 + t * sgn R ((M *ᵥ σ) p))
      = ∑ S : P → ZMod 2,
          t ^ hammingNorm S * ∑ σ : E → ZMod 2, sgn R ((c + Mᵀ *ᵥ S) ⬝ᵥ σ) := by
        simp_rw [prod_one_add_eq_sum, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun σ _ => ?_
        rw [dotProduct_mulVec, ← mulVec_transpose, add_dotProduct, sgn_add]
        ring
    _ = _ := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [sum_sgn_dotProduct]
        by_cases h : Mᵀ *ᵥ S = c
        · rw [ite_cond_eq_true _ _ (eq_true ((hc S).mpr h)), ite_cond_eq_true _ _ (eq_true h)]
          ring
        · rw [ite_cond_eq_false _ _ (eq_false fun h' => h ((hc S).mp h')),
            ite_cond_eq_false _ _ (eq_false h)]
          ring

end

end D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion
