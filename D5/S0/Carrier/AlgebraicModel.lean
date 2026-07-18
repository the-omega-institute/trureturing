/- GID: D5/S0/Carrier/AlgebraicModel
   generality: G
   mirror-B: D5/B/S0/Carrier/AlgebraicModel
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Quadratic quotient with explicit golden conjugate, trace, and norm. -/

import D5.S0.Carrier.Norm
import Mathlib.RingTheory.AdjoinRoot

namespace D5.S0.Carrier

open Polynomial

noncomputable section

/-- The monic polynomial whose root is the golden generator. -/
def goldenPolynomial : ℤ[X] := X ^ 2 - X - 1

/-- The quotient presentation `Z[t]/(t^2-t-1)`. -/
abbrev GoldenAdjoinRoot := AdjoinRoot goldenPolynomial

private theorem goldenPolynomial_phi :
    goldenPolynomial.eval₂ (Int.castRingHom GoldenInt) phi = 0 := by
  simp [goldenPolynomial, phi_sq]

/-- Evaluate the quotient root at the coordinate generator. -/
def goldenAdjoinRootToInt : GoldenAdjoinRoot →+* GoldenInt :=
  AdjoinRoot.lift (Int.castRingHom GoldenInt) phi goldenPolynomial_phi

private theorem goldenAdjoinRoot_root_sq :
    AdjoinRoot.root goldenPolynomial ^ 2 =
      AdjoinRoot.root goldenPolynomial + 1 := by
  have h := AdjoinRoot.mk_self (f := goldenPolynomial)
  change AdjoinRoot.root goldenPolynomial ^ 2 -
    AdjoinRoot.root goldenPolynomial - 1 = 0 at h
  linear_combination h

/-- Rebuild a quotient class from its integral `(1, phi)` coordinates. -/
def goldenIntToAdjoinRoot : GoldenInt →+* GoldenAdjoinRoot where
  toFun x :=
    (x.a : GoldenAdjoinRoot) +
      (x.b : GoldenAdjoinRoot) * AdjoinRoot.root goldenPolynomial
  map_one' := by simp
  map_mul' x y := by
    simp only [a_mul, b_mul]
    push_cast
    linear_combination
      -(x.b * y.b : GoldenAdjoinRoot) * goldenAdjoinRoot_root_sq
  map_zero' := by simp
  map_add' x y := by
    simp only [a_add, b_add]
    push_cast
    ring

private theorem goldenAdjoinRootToInt_toAdjoinRoot (x : GoldenInt) :
    goldenAdjoinRootToInt (goldenIntToAdjoinRoot x) = x := by
  ext <;> simp [goldenAdjoinRootToInt, goldenIntToAdjoinRoot]

private theorem goldenIntToAdjoinRoot_toInt (x : GoldenAdjoinRoot) :
    goldenIntToAdjoinRoot (goldenAdjoinRootToInt x) = x := by
  have hcomp :
      goldenIntToAdjoinRoot.comp goldenAdjoinRootToInt =
        RingHom.id GoldenAdjoinRoot := by
    apply AdjoinRoot.ringHom_ext
    · ext z
      simp [goldenAdjoinRootToInt, goldenIntToAdjoinRoot]
    · simp [goldenAdjoinRootToInt, goldenIntToAdjoinRoot]
  exact DFunLike.congr_fun hcomp x

/-- The coordinate golden ring is the polynomial quotient at the golden root. -/
def goldenAdjoinRootEquiv : GoldenAdjoinRoot ≃+* GoldenInt where
  toFun := goldenAdjoinRootToInt
  invFun := goldenIntToAdjoinRoot
  left_inv := goldenIntToAdjoinRoot_toInt
  right_inv := goldenAdjoinRootToInt_toAdjoinRoot
  map_mul' := goldenAdjoinRootToInt.map_mul
  map_add' := goldenAdjoinRootToInt.map_add

/-- Exact formal echo of the carrier, conjugation, trace, and norm formulas. -/
theorem golden_algebraic_model_spec (a b : ℤ) :
    goldenAdjoinRootEquiv (AdjoinRoot.root goldenPolynomial) = phi ∧
      conj ⟨a, b⟩ = ⟨a + b, -b⟩ ∧
      trace ⟨a, b⟩ = 2 * a + b ∧
      norm ⟨a, b⟩ = a ^ 2 + a * b - b ^ 2 := by
  simp [goldenAdjoinRootEquiv, goldenAdjoinRootToInt, conj, trace, norm,
    pow_two]

end

end D5.S0.Carrier
