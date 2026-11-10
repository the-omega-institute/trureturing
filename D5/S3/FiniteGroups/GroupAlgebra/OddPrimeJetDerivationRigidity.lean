/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDerivationRigidity
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetDerivationRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Derivation.Basic]
   utility: none
   digest: Derivations classify removable highest jets over arbitrary fields. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDeformation
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity

open Polynomial Finset Module OddPrimeJetDeformation
open scoped BigOperators

universe uK
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type uK} [Field K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p
local notation "E" => Multiplicative K
local notation "D" => derivativeEnd (p := p) (K := K)

private theorem leibniz_of_commutator (q Q : K →ₗ[F] K)
    (h : ∀ a s : K, a * Q s - Q (a*s) = q a * s) (a b : K) :
    q (a*b) = a * q b + b * q a := by
  have ha := h a 1
  have hb := h b 1
  have hab := h (a*b) 1
  have hs := h a b
  simp only [mul_one] at ha hb hab
  linear_combination hab - hs - a * hb + b * ha

private theorem necessary (q : K →ₗ[F] K) (hq1 : q 1 = 0)
    (φ : E ≃* E) (P : V ≃ₗ[F] V)
    (hP : ∀ (g : E) (v : V), P (originalRepresentation (p := p) q g v) =
      ordinaryRepresentation (φ g) (P v)) :
    ∀ a b : K, q (a*b) = a * q b + b * q a := by
  let c : K := automorphismLinear (p := p) φ 1
  have hc : c ≠ 0 := by
    intro hz
    have hφ : φ (Multiplicative.ofAdd (1 : K)) = 1 := congrArg Multiplicative.ofAdd hz
    have hx := φ.injective (hφ.trans φ.map_one.symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd hx)
  let S : V ≃ₗ[K] V := diagonalScale c hc
  let P' : V ≃ₗ[F] V := P.trans (S.restrictScalars F)
  have hnorm (x : K) (v : V) :
      P' (jetOperator q x v) = (automorphismLinear (p := p) φ x / c) • D (P' v) := by
    change S (P (jetOperator q x v)) = _
    rw [log_intertwining q φ P hP, S.map_smul, diagonalScale_derivative]
    simp only [P', LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      smul_smul, div_eq_mul_inv, S]
  have hD : ∀ v : V, P' (D v) = D (P' v) := by
    intro v
    have h := hnorm 1 v
    simpa only [jetOperator, hq1, zero_smul, add_zero, one_smul,
      ← show c = automorphismLinear (p := p) φ 1 from rfl, div_self hc, one_smul] using h
  apply leibniz_of_commutator q (constantCommutator P' hD)
  intro a s
  exact structural_commutator P' hD a (q a)
    (automorphismLinear (p := p) φ a / c) (hnorm a) s

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetDerivationRigidity
