/- GID: D5/S3/ArithUnits/MultiplierRootPolynomialSelection
   generality: G
   mirror-B: D5/B/S3/ArithUnits/MultiplierRootPolynomialSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Multiplier invariance confines root-polynomial coefficients to order-resonant degrees. -/

import Mathlib

/- Library-search audit trail (2026-09-28):
   * `Multiset.pow_smul_esymm` gives the scaling weight of each elementary symmetric
     function; `Multiset.prod_X_sub_C_coeff` gives its exact Vieta coefficient.
   * The existing multiplier obstruction controls orbit cardinality, and the
     Newton-power-sum module reconstructs split polynomials in characteristic zero;
     neither states this characteristic-independent coefficient-support law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.MultiplierRootPolynomialSelection

open Polynomial

open Classical in
/-- A multiplier-invariant finite root set has no coefficient at a degree whose
codimension is a nontrivial multiplier weight. -/
theorem coeff_zero_of_mul_invariant
    {K : Type*} [Field K] (S : Finset K) (u : K) (j : ℕ)
    (hu : u ≠ 0)
    (hinv : S.image (fun x => u * x) = S)
    (hj : j ≤ S.card)
    (hpow : u ^ (S.card - j) ≠ 1) :
    (S.prod fun x => X - C x).coeff j = 0 := by
  classical
  have hinj : Function.Injective (fun x : K => u * x) :=
    fun _ _ h => mul_left_cancel₀ hu h
  have hmap : S.val.map (fun x => u * x) = S.val := by
    calc
      S.val.map (fun x => u * x) = (S.image (fun x => u * x)).val :=
        (Finset.image_val_of_injOn hinj.injOn).symm
      _ = S.val := congrArg Finset.val hinv
  have hscale : u ^ (S.card - j) * S.val.esymm (S.card - j) =
      S.val.esymm (S.card - j) := by
    simpa only [smul_eq_mul, hmap] using
      (Multiset.pow_smul_esymm u (S.card - j) S.val)
  have hzero : S.val.esymm (S.card - j) = 0 :=
    eq_zero_of_mul_eq_self_left hpow hscale
  calc
    (S.prod fun x => X - C x).coeff j =
        (-1) ^ (S.card - j) * S.val.esymm (S.card - j) := by
          simpa only [Finset.prod, Finset.card] using
            (Multiset.prod_X_sub_C_coeff S.val (k := j) hj)
    _ = 0 := by rw [hzero, mul_zero]

example :
    (({1, 2, 4} : Finset (ZMod 7)).image (fun x => 2 * x) = {1, 2, 4}) ∧
      (2 : ZMod 7) ^ 3 = 1 ∧
        (({1, 2, 4} : Finset (ZMod 7)).prod fun x => X - C x).coeff 0 ≠ 0 := by
  constructor
  · decide
  constructor
  · decide
  · norm_num [coeff_zero_eq_eval_zero, eval_prod, Finset.prod_insert]
    decide

#print axioms coeff_zero_of_mul_invariant

end D5.S3.ArithUnits.MultiplierRootPolynomialSelection
