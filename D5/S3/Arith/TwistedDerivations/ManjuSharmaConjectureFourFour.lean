/- GID: D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour
   generality: I
   mirror-B: D5/B/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The printed prime-power twisted-derivation criterion on actual cyclotomic integer rings. -/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace D5.S3.Arith.TwistedDerivations.ManjuSharmaConjectureFourFour

noncomputable section

open NumberField Matrix

/-- Integral innerness, with the generator required to belong to the actual integer ring. -/
def IsInner {O : Type*} [CommRing O] (σ τ : O →ₐ[ℤ] O) (D : O →ₗ[ℤ] O) : Prop :=
  ∃ γ : O, ∀ x : O, D x = γ * τ x - σ x * γ

/-- The printed denominator is `p^e`, without replacing it by the determinant. -/
def PrintedIntegralTest {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p e : ℕ) (A : Matrix ι ι ℤ) (C : ι → ℤ) : Prop :=
  ∃ X : ι → ℤ, ∀ i,
    ((p : ℚ) ^ e)⁻¹ *
      ((A.adjugate.map (Int.castRingHom ℚ)) *ᵥ (fun j => (C j : ℚ))) i = (X i : ℚ)

/-- Conjecture 4.4, including both additional sufficient assertions.
The matrix is the actual multiplication operator; no integral solution of `D z` is assumed. -/
def claim : Prop :=
  ∀ (p k : ℕ), p.Prime → k ≠ 1 → 3 ≤ p ^ k →
  ∀ (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p ^ k} ℚ K]
    [NeZero (p ^ k)] (ζ : K) (hζ : IsPrimitiveRoot ζ (p ^ k)),
  let z := hζ.toInteger
  let pb := hζ.integralPowerBasis
  ∀ (σ τ : RingOfIntegers K →ₐ[ℤ] RingOfIntegers K), σ ≠ τ →
  ∀ (u v e m : ℕ),
    u < p ^ k → v < p ^ k → Nat.Coprime u (p ^ k) → Nat.Coprime v (p ^ k) →
    u ≠ v → σ z = z ^ u → τ z = z ^ v → 0 < m → ¬ p ∣ m →
    v = u + p ^ e * m →
  ∀ (D : RingOfIntegers K →ₗ[ℤ] RingOfIntegers K),
    (∀ x y, D (x * y) = D x * τ y + σ x * D y) →
  let A := Algebra.leftMulMatrix pb.basis (τ z - σ z)
  let C := fun i => pb.basis.repr (D z) i
  (IsInner σ τ D ↔ PrintedIntegralTest p e A C) ∧
    ((∀ i, (p : ℤ) ^ e ∣ C i) → IsInner σ τ D) ∧
    ((∀ i, (p : ℤ) ∣ C i) → IsInner σ τ D)

abbrev K4 := CyclotomicField 4 ℚ
abbrev O4 := RingOfIntegers K4

def root : K4 := IsCyclotomicExtension.zeta 4 ℚ K4
private theorem root_primitive : IsPrimitiveRoot root 4 :=
  IsCyclotomicExtension.zeta_spec 4 ℚ K4

def z : O4 := root_primitive.toInteger

def pb : PowerBasis ℤ O4 := root_primitive.integralPowerBasis

#check root_primitive.toInteger_isPrimitiveRoot
#check IsPrimitiveRoot.pow_div_gcd
#check IsPrimitiveRoot.eq_neg_one_of_two_right
#check Zsqrtd.lift
#check Zsqrtd.lift_injective
#print axioms claim

end
end D5.S3.Arith.TwistedDerivations.ManjuSharmaConjectureFourFour
