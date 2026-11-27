/- GID: D5/S3/Combinatorics/Matroids/UniformCircuitBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/UniformCircuitBasis
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: An integral basis adapted to a coordinate sum and a vector of positive weights. -/

module

public import D5.S3.Combinatorics.Matroids.RankTwoCircuitInvariantFactors
public import Mathlib.LinearAlgebra.Dual.Basis

/-! An integral change of basis that retains the sum of coordinates. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.UniformCircuitBasis

open Finset RankTwoCircuitInvariantFactors
set_option autoImplicit false

/-- The sum of coordinates of a finite vector. -/
def sumCovector (I : Type*) [Fintype I] : (I → ℤ) →ₗ[ℤ] ℤ where
  toFun f := ∑ i, f i
  map_add' f g := sum_add_distrib
  map_smul' d f := by
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

private def sumSplit (k : ℕ) :
    (Fin (k + 1) → ℤ) ≃ₗ[ℤ] ℤ × (Fin k → ℤ) where
  toFun f := (∑ i, f i, fun i => f i.succ)
  invFun p := Fin.cons (p.1 - ∑ i, p.2 i) p.2
  left_inv f := by
    change Fin.cons ((∑ i, f i) - ∑ i : Fin k, f i.succ) (Fin.tail f) = f
    rw [Fin.sum_univ_succ, add_sub_cancel_right, Fin.cons_self_tail]
  right_inv p := by
    apply Prod.ext
    · simp [Fin.sum_univ_succ, sub_add_cancel]
    · funext i
      rfl
  map_add' f g := Prod.ext sum_add_distrib rfl
  map_smul' d f := Prod.ext (by
    change (∑ i, d • f i) = d • ∑ i, f i
    exact (Finset.smul_sum ..).symm) rfl

/-- A positive integral weight vector is a multiple of one element of an
integral basis, with multiplier the gcd of the weights. -/
theorem weight_vector_in_basis (k : ℕ) (w : Fin (k + 1) → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ b : Module.Basis (Fin (k + 1)) ℤ (Fin (k + 1) → ℤ),
      (fun i => (w i : ℤ)) = ((univ.gcd w : ℕ) : ℤ) • b 0 := by
  classical
  obtain ⟨coordinates, hcoordinates⟩ := exists_sum_coordinates (A := ℤ) k w hw
  let E := coordinates.trans (Fin.consLinearEquiv ℤ (fun _ : Fin (k + 1) => ℤ))
  let standard := Pi.basisFun ℤ (Fin (k + 1))
  let dualCoordinates := (standard.map E.symm).dualBasis
  let b := dualCoordinates.map (standard.constr ℤ).symm
  refine ⟨b, funext fun i => ?_⟩
  have hb : b 0 i = (coordinates (standard i)).1 := by
    change (standard.constr ℤ).symm (dualCoordinates 0) i = _
    rw [Module.Basis.constr_symm_apply, Module.Basis.dualBasis_apply]
    change (standard.map E.symm).repr (standard i) 0 = _
    rw [Module.Basis.map_repr, LinearEquiv.symm_symm]
    exact (congrFun (Module.Basis.equivFun_apply standard (E (standard i))) 0).symm.trans
      (by simp [standard, E, Pi.basisFun])
  change (w i : ℤ) = ((univ.gcd w : ℕ) : ℤ) * b 0 i
  rw [hb]
  have h := hcoordinates (standard i)
  rw [nsmul_eq_mul] at h
  rw [h]
  simp [standard, Pi.basisFun, Pi.single_apply, mul_ite]

/-- There is an adapted basis whose first vector has coordinate sum one and
whose second vector carries the tail gcd of the positive weight vector. -/
theorem exists_adapted_weight_basis (k : ℕ) (w : Fin (k + 2) → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ b : Module.Basis (Fin (k + 2)) ℤ (Fin (k + 2) → ℤ),
      sumCovector _ (b 0) = 1 ∧
      (fun i => (w i : ℤ)) = ((∑ i, w i : ℕ) : ℤ) • b 0 +
        ((univ.gcd (fun i : Fin (k + 1) => w i.succ) : ℕ) : ℤ) • b (Fin.succ 0) := by
  let tail : Fin (k + 1) → ℕ := fun i => w i.succ
  obtain ⟨tailBasis, htail⟩ := weight_vector_in_basis k tail (fun i => hw i.succ)
  let coordinates := (sumSplit (k + 1)).trans
    (((LinearEquiv.refl ℤ ℤ).prodCongr tailBasis.equivFun).trans
      (Fin.consLinearEquiv ℤ (fun _ : Fin (k + 2) => ℤ)))
  let standard := Pi.basisFun ℤ (Fin (k + 2))
  let b := standard.map coordinates.symm
  have hb (i : Fin (k + 2)) : coordinates (b i) = standard i := LinearEquiv.apply_symm_apply _ _
  have h0 (f : Fin (k + 2) → ℤ) : coordinates f 0 = sumCovector _ f := rfl
  refine ⟨b, ?_, ?_⟩
  · rw [← h0, hb]
    simp [standard, Pi.basisFun]
  · apply coordinates.injective
    rw [map_add, map_zsmul, map_zsmul, hb, hb]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [h0, standard, Pi.basisFun, sumCovector, Int.cast_sum]
    · have ht : coordinates (fun j => (w j : ℤ)) i.succ =
          tailBasis.equivFun (fun j => (tail j : ℤ)) i := rfl
      rw [ht, htail, map_zsmul, Pi.smul_apply, Module.Basis.equivFun_self]
      have hOne : i.succ = 1 ↔ i = 0 := by
        change i.succ = (0 : Fin (k + 1)).succ ↔ i = 0
        exact Fin.succ_inj
      simp [standard, Pi.basisFun, Pi.single_apply, Fin.succ_ne_zero, hOne, tail,
        eq_comm (a := (0 : Fin (k + 1)))]

end D5.S3.Combinatorics.Matroids.UniformCircuitBasis
