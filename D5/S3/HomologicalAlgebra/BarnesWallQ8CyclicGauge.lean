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

/-- The coordinate map for one of the order-four subgroups. -/
def power (r : Fin 3) (a : ZMod 4) : Q8 :=
  generator r ^ a.val

theorem power_add (r : Fin 3) (a b : ZMod 4) : power r (a + b) = power r a * power r b := by
  revert r a b
  decide +kernel

/-- The central involution of the three cyclic subgroups. -/
def center : Q8 := i ^ 2

theorem power_two (r : Fin 3) : power r 2 = center := by
  revert r
  decide +kernel

/-- The binary carry cochain on the subgroup, scaled by the candidate exponent. -/
def beta (e : ZMod 2) (a b : ZMod 4) : ZMod 2 :=
  e * (a.val : ZMod 2) * ((b.val / 2 : ℕ) : ZMod 2)

/-- The explicit tensorator absorbs the entire cyclic restriction. -/
theorem beta_coboundary (e : ZMod 2) (r : Fin 3) (a b c : ZMod 4) :
    beta e b c - beta e (a + b) c + beta e a (b + c) - beta e a b =
      e * etaExponent (power r a, power r b, power r c) := by
  revert e r a b c
  decide +kernel

/-- In the inflated global gauge, the central involution has trivial slant
cochain. The action at this flux therefore has no slant multiplier. -/
theorem central_slant_exponent (a b : Q8) :
    etaExponent (center, a, b) - etaExponent (a, center, b) + etaExponent (a, b, center) =
      0 := by
  have hz : (BarnesWallQ8CohomologyDetector.quotientCoordinates center).toAdd = (0, 0) := by
    decide
  simp [etaExponent, BarnesWallQ8CohomologyDetector.etaPolynomial, hz]

/-- The sum of the three cyclic half-braiding exponents is the global
candidate exponent. Each of the two possible inflations is distinguished
by this sum, although all three cyclic cohomology classes vanish. -/
theorem cyclic_phase_product_exponent (e : ZMod 2) :
    (∑ _r : Fin 3, (beta e 1 2 - beta e 2 1)) = e := by
  rw [Fin.sum_univ_three]
  revert e
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
  have hcases : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide +kernel
  have he' := (hcases e).resolve_left he
  have hunit : (beta 1 1 2 - beta 1 2 1 : ZMod 2).val = 1 := by decide
  simp only [he', hunit, pow_one, neg_one_mul] at htransport
  have hc : 0 < ∏ r, cyclicTrace r := Finset.prod_pos (fun r _ => hcyclic r)
  rw [Fin.prod_univ_three] at hc hglobal
  rw [htransport 0, htransport 1, htransport 2] at hc
  simp only [neg_mul, mul_neg, neg_neg, neg_pos] at hc
  exact (not_lt_of_ge (le_of_lt hglobal)) hc

#print axioms zero_exponent_of_positive_trace_product

end D5.S3.HomologicalAlgebra.BarnesWallQ8CyclicGauge
