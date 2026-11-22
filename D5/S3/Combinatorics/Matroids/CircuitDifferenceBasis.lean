/- GID: D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitDifferenceBasis
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Difference coordinates around two representatives separate disjoint faces. -/

module

public import D5.S3.Combinatorics.Matroids.UniformCircuitBasis
import Mathlib.LinearAlgebra.Transvection.Basic

/-! Difference coordinates with a separate representative for one block. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.CircuitDifferenceBasis

open Finset

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Subtract the local representative inside a block and the global
representative elsewhere. The new coordinate at the local representative
is the sum over its block, and the coordinate at the global representative
is the sum over the whole index set. -/
theorem exists_difference_basis (H : Finset I) (p q : I) (hp : p ∉ H) (hq : q ∈ H) :
    ∃ b : Module.Basis I ℤ (I → ℤ),
      b p = Pi.single p 1 ∧
      (∀ i, i ≠ p → b i = Pi.single i 1 - Pi.single (if i ∈ H.erase q then q else p) 1) ∧
      ∀ (x : I → ℤ) i, b.equivFun x i =
        if i = p then ∑ j, x j else if i = q then ∑ j ∈ H, x j else x i := by
  let e (i : I) : I → ℤ := Pi.single i 1
  let s (F : Finset I) : (I → ℤ) →ₗ[ℤ] ℤ := ∑ i ∈ F, LinearMap.proj i
  have hs (F : Finset I) (x : I → ℤ) : s F x = ∑ i ∈ F, x i := by
    simp [s, LinearMap.sum_apply]
  have he (F : Finset I) (i : I) : s F (e i) = if i ∈ F then 1 else 0 := by
    rw [hs]
    simp [e, Pi.single_apply]
  let T := (univ : Finset I).erase p
  let U := H.erase q
  have hpT : p ∉ T := notMem_erase p _
  have hqU : q ∉ U := notMem_erase q _
  have hpU : p ∉ U := fun h => hp (mem_of_mem_erase h)
  have hpq : p ≠ q := fun h => hp (h ▸ hq)
  have hqT : q ∈ T := mem_erase.mpr ⟨hpq.symm, mem_univ _⟩
  have hTp : s T (-e p) = 0 := by simp [he, hpT]
  have hUq : s U (-e q) = 0 := by simp [he, hqU]
  let global := LinearEquiv.transvection hTp
  let blockShift := LinearEquiv.transvection hUq
  let transform := blockShift.trans global
  let b := (Pi.basisFun ℤ I).map transform
  have hG (x : I → ℤ) : global x = x - s T x • e p := by
    change x + s T x • -e p = _
    rw [smul_neg, sub_eq_add_neg]
  have hL (x : I → ℤ) : blockShift x = x - s U x • e q := by
    change x + s U x • -e q = _
    rw [smul_neg, sub_eq_add_neg]
  have hb (i : I) : b i = global (blockShift (e i)) := by
    rw [Module.Basis.map_apply, Pi.basisFun_apply]
    rfl
  have hGinv (x : I → ℤ) : global.symm x = x + s T x • e p := by
    change x + s T x • -(-e p) = _
    rw [neg_neg]
  have hLinv (x : I → ℤ) : blockShift.symm x = x + s U x • e q := by
    change x + s U x • -(-e q) = _
    rw [neg_neg]
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hb, hL, he, ite_eq_right hpU, zero_smul, sub_zero,
      hG, he, ite_eq_right hpT, zero_smul, sub_zero]
  · intro i hi
    have hiT : i ∈ T := mem_erase.mpr ⟨hi, mem_univ _⟩
    by_cases hiU : i ∈ U
    · rw [hb, hL, he, ite_eq_left hiU, one_smul, hG, map_sub, he, he,
        ite_eq_left hiT, ite_eq_left hqT, sub_self, zero_smul, sub_zero, ite_eq_left hiU]
    · rw [hb, hL, he, ite_eq_right hiU, zero_smul, sub_zero, hG, he, ite_eq_left hiT,
        one_smul, ite_eq_right hiU]
  · intro x i
    change blockShift.symm (global.symm x) i = _
    rw [hLinv, hGinv, map_add, map_smul, he, ite_eq_right hpU, smul_zero, add_zero]
    change x i + s T x * e p i + s U x * e q i = _
    by_cases hip : i = p
    · subst i
      rw [ite_eq_left rfl, hs, ← sum_erase_add _ x (mem_univ p)]
      simp [e, hpq, T, add_comm]
    · by_cases hiq : i = q
      · subst i
        rw [ite_eq_right hip, ite_eq_left rfl, hs U, ← sum_erase_add _ x hq]
        simpa [e, hpq, hpq.symm, U] using add_comm (x q) (∑ j ∈ U, x j)
      · simp [e, hip, hiq, Ne.symm hip, Ne.symm hiq]

end D5.S3.Combinatorics.Matroids.CircuitDifferenceBasis
