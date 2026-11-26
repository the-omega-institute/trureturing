/- GID: D5/S3/HomologicalAlgebra/BarnesWallQ8CyclicGauge
   generality: I
   mirror-B: D5/B/S3/HomologicalAlgebra/BarnesWallQ8CyclicGauge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.SpecificGroups.Quaternion]
   utility: none
   digest: The three cyclic tensorators detect the inflated quaternion anomaly by the product of the centralizer signs. -/

import D5.S3.HomologicalAlgebra.BarnesWallQ8CohomologyDetector

/-! The cyclic normalizations of the quaternion detector in characteristic two.
On each of the three order-four subgroups, the possible nonzero anomaly has
a trivializing two-cochain. Its centralizer ratio at the central involution
is nontrivial, and the product over the three generators retains that sign. -/

open scoped BigOperators

set_option autoImplicit false

namespace D5.S3.HomologicalAlgebra.BarnesWallQ8CyclicGauge

open BarnesWallQ8CohomologyDetector (Q8 i j k etaExponent)

/-- The three order-four generators used in the detector. -/
def generator : Fin 3 → Q8
  | 0 => i
  | 1 => j
  | 2 => k

/-- The cyclic coordinate homomorphism for a quaternion generator. -/
def power (r : Fin 3) : Multiplicative (ZMod 4) →* Q8 where
  toFun a := generator r ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    revert r a b
    decide +kernel

/-- The binary carry cochain on the subgroup, scaled by the candidate exponent. -/
def beta (e : ZMod 2) (a b : ZMod 4) : ZMod 2 :=
  e * (a.val : ZMod 2) * ((b.val / 2 : ℕ) : ZMod 2)

/-- The explicit tensorator absorbs the entire cyclic restriction. -/
theorem beta_coboundary (e : ZMod 2) (r : Fin 3) (a b c : ZMod 4) :
    beta e b c - beta e (a + b) c + beta e a (b + c) - beta e a b =
      e * etaExponent (power r (Multiplicative.ofAdd a), power r (Multiplicative.ofAdd b),
        power r (Multiplicative.ofAdd c)) := by
  revert e r a b c
  decide +kernel

/-- If the three cyclic traces and the global trace product are positive,
the transported half-braidings force the candidate exponent to be zero. -/
theorem zero_exponent_of_positive_trace_product (e : ZMod 2)
    (globalTrace cyclicTrace : Fin 3 → ℝ)
    (hglobal : 0 < ∏ r, globalTrace r)
    (hcyclic : ∀ r, 0 < cyclicTrace r)
    (htransport : ∀ r, cyclicTrace r =
      (-1 : ℝ) ^ (beta e 1 2 - beta e 2 1).val * globalTrace r) :
    e = 0 := by
  by_contra he
  have hphase : beta e 1 2 - beta e 2 1 = e := by
    have h := beta_coboundary e 0 1 1 1
    let g := power 0 (Multiplicative.ofAdd (1 : ZMod 4))
    have heta : etaExponent (g, g, g) = 1 := by decide +kernel
    change beta e 1 1 - beta e 2 1 + beta e 1 2 - beta e 1 1 =
      e * etaExponent (g, g, g) at h
    calc
      beta e 1 2 - beta e 2 1 =
          beta e 1 1 - beta e 2 1 + beta e 1 2 - beta e 1 1 := by abel
      _ = e := by simpa [heta] using h
  have hcases : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide +kernel
  have he' := (hcases e).resolve_left he
  have hval : (1 : ZMod 2).val = 1 := by decide
  have hneg (r : Fin 3) : cyclicTrace r = -globalTrace r := by
    rw [htransport r, hphase, he', hval, pow_one, neg_one_mul]
  have hc : 0 < ∏ r, cyclicTrace r := Finset.prod_pos (fun r _ => hcyclic r)
  rw [Fin.prod_univ_three] at hc hglobal
  rw [hneg 0, hneg 1, hneg 2] at hc
  simp only [neg_mul, mul_neg, neg_neg] at hc
  exact (not_lt_of_ge (le_of_lt hglobal)) (neg_pos.mp hc)

#print axioms zero_exponent_of_positive_trace_product

end D5.S3.HomologicalAlgebra.BarnesWallQ8CyclicGauge
