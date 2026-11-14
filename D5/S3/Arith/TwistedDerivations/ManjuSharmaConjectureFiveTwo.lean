/- GID: D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo
   generality: I
   mirror-B: D5/B/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.claim; result=D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.result; claim=D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.claim
   digest: The complete printed outer-derivation criterion and strict inclusion on cyclotomic integer rings. -/

import D5.S3.Arith.TwistedDerivations.ManjuSharmaConjectureFourFour
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The outer quotient and both assertions of the printed prime-power conjecture. -/

namespace D5.S3.Arith.TwistedDerivations.ManjuSharmaConjectureFiveTwo

noncomputable section

open NumberField

/-- The integer submodule of all maps satisfying the full twisted Leibniz law. -/
def derivations {O : Type*} [CommRing O] (σ τ : O →ₐ[ℤ] O) :
    Submodule ℤ (O →ₗ[ℤ] O) where
  carrier := {D | ∀ x y, D (x * y) = D x * τ y + σ x * D y}
  zero_mem' := by simp
  add_mem' := by
    intro D E hD hE x y
    simp only [LinearMap.add_apply, hD x y, hE x y]
    ring
  smul_mem' := by
    intro a D hD x y
    change a • D (x * y) = (a • D x) * τ y + σ x * (a • D y)
    rw [hD x y]
    simp only [zsmul_eq_mul]
    ring

/-- Inner derivations have a single integral multiplier valid on the entire ring. -/
def inner {O : Type*} [CommRing O] (σ τ : O →ₐ[ℤ] O) :
    Submodule ℤ (derivations σ τ) where
  carrier := {D | ManjuSharmaConjectureFourFour.IsInner σ τ D.val}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro x
    simp
  add_mem' := by
    rintro D E ⟨γ, hγ⟩ ⟨δ, hδ⟩
    refine ⟨γ + δ, ?_⟩
    intro x
    change D.val x + E.val x = _
    rw [hγ x, hδ x]
    ring
  smul_mem' := by
    rintro a D ⟨γ, hγ⟩
    refine ⟨a • γ, ?_⟩
    intro x
    change a • D.val x = _
    rw [hγ x]
    simp only [zsmul_eq_mul]
    ring

/-- The actual class in the quotient of twisted derivations by inner derivations. -/
def outerClass {O : Type*} [CommRing O] (σ τ : O →ₐ[ℤ] O)
    (D : derivations σ τ) : (derivations σ τ) ⧸ inner σ τ :=
  (inner σ τ).mkQ D

private theorem outer_nonzero_iff {O : Type*} [CommRing O]
    (σ τ : O →ₐ[ℤ] O) (D : derivations σ τ) :
    outerClass σ τ D ≠ 0 ↔ ¬ ManjuSharmaConjectureFourFour.IsInner σ τ D.val := by
  change ¬ (Submodule.Quotient.mk D : (derivations σ τ) ⧸ inner σ τ) = 0 ↔ _
  exact not_congr Submodule.Quotient.mk_eq_zero

/-- The full source conjunction, with both orientations of each distinct twist pair.
The positive source factorization is applied in increasing exponent order; the actual
matrix remains multiplication by tau(z)-sigma(z), including for a reversed pair. -/
def claim : Prop :=
  ∀ (p k : ℕ), p.Prime → k ≠ 1 → 3 ≤ p ^ k →
  ∀ (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p ^ k} ℚ K]
    [NeZero (p ^ k)] (ζ : K) (hζ : IsPrimitiveRoot ζ (p ^ k)),
  let z := hζ.toInteger
  ∀ (pb : PowerBasis ℤ (RingOfIntegers K)),
    pb.gen = z → pb.dim = p ^ (k - 1) * (p - 1) →
  ∀ (σ τ : RingOfIntegers K →ₐ[ℤ] RingOfIntegers K), σ ≠ τ →
  ∀ (u v e m : ℕ),
    0 < u → 0 < v → u < p ^ k → v < p ^ k →
    Nat.Coprime u (p ^ k) → Nat.Coprime v (p ^ k) →
    u ≠ v → σ z = z ^ u → τ z = z ^ v → 0 < m → ¬ p ∣ m →
    (v = u + p ^ e * m ∨ u = v + p ^ e * m) →
  let A := Algebra.leftMulMatrix pb.basis (τ z - σ z)
  (∀ D : derivations σ τ,
    let C := fun i => pb.basis.repr (D.val z) i
    outerClass σ τ D ≠ 0 ↔ ¬ ManjuSharmaConjectureFourFour.PrintedIntegralTest p e A C) ∧
    inner σ τ < ⊤ ∧ ∃ D : derivations σ τ, outerClass σ τ D ≠ 0

/-- The entire printed Conjecture 5.2 is false, including its universal conjunction. -/
theorem result : ¬ claim := by
  intro h
  let σ := AlgHom.id ℤ ManjuSharmaConjectureFourFour.O4
  have hne : σ ≠ ManjuSharmaConjectureFourFour.tau := by
    intro heq
    have hz : ManjuSharmaConjectureFourFour.z ^ 1 =
        ManjuSharmaConjectureFourFour.z ^ 3 := by
      calc
        _ = σ ManjuSharmaConjectureFourFour.z := by simp [σ]
        _ = ManjuSharmaConjectureFourFour.tau ManjuSharmaConjectureFourFour.z :=
          congrArg (fun f => f ManjuSharmaConjectureFourFour.z) heq
        _ = _ := ManjuSharmaConjectureFourFour.counterinstance_root_values.2
    have hp : IsPrimitiveRoot ManjuSharmaConjectureFourFour.z 4 :=
      ManjuSharmaConjectureFourFour.root_primitive.toInteger_isPrimitiveRoot
    have hi := hp.pow_inj (i := 1) (j := 3) (by decide) (by decide) hz
    omega
  letI : IsCyclotomicExtension {2 ^ 2} ℚ ManjuSharmaConjectureFourFour.K4 := by
    norm_num
    exact CyclotomicField.isCyclotomicExtension 4 ℚ
  have hc := h 2 2 (by decide) (by decide) (by decide)
    ManjuSharmaConjectureFourFour.K4 ManjuSharmaConjectureFourFour.root
    ManjuSharmaConjectureFourFour.root_primitive
    ManjuSharmaConjectureFourFour.orderedPb rfl (by decide)
    σ ManjuSharmaConjectureFourFour.tau hne
    1 3 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by simp [σ]) ManjuSharmaConjectureFourFour.counterinstance_root_values.2
    (by decide) (by decide) (Or.inl (by decide))
  let d : derivations σ ManjuSharmaConjectureFourFour.tau :=
    ⟨ManjuSharmaConjectureFourFour.derivation, by
      simpa [derivations, σ] using ManjuSharmaConjectureFourFour.derivation_twisted⟩
  have hout : outerClass σ ManjuSharmaConjectureFourFour.tau d ≠ 0 :=
    (outer_nonzero_iff _ _ d).2 ManjuSharmaConjectureFourFour.derivation_not_inner
  exact (hc.1 d).mp hout (by simpa only [σ, d, AlgHom.id_apply] using ManjuSharmaConjectureFourFour.printed_test)

#print axioms claim
#print axioms result

end
end D5.S3.Arith.TwistedDerivations.ManjuSharmaConjectureFiveTwo
