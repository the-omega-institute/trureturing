/- GID: D5/S3/VertexAlgebra/ActualTensorGroundIntersection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ActualTensorGroundIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative actual currents force every nonzero invariant tensor submodule to meet the selected finite ground. -/

/- proof_shape: nonzero_current_stable_submodule_meets_ground: content
admission_basis: escape-witness
escape_witness: The simultaneous finite-coordinate maximum-degree descent and inverse-Gram transport are new tensor-level content; the proof uses only the actual finite ground, actual currents, polynomial partials and pinned matrix inverse.
-/
import D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
import D5.S3.VertexAlgebra.LatticeHalfFockTensorFields
import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import D5.S3.VertexAlgebra.LatticeActualAnnihilation
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualTensorGroundIntersection

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeTwistedGroundRealization LatticeSugawaraCurrents MvPolynomial
open D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity.API
open scoped BigOperators TensorProduct

/-- The actual selected finite ground, in its existing function coordinates. -/
private def coordinates (D : LatticeData) (hu : IsUnit D.G.det) :
    ActualTensor D hu ≃ₗ[ℂ] (Half (groundRank D hu) → Oscillator D) :=
  TensorProduct.piScalarRight ℂ ℂ (Oscillator D) (Half (groundRank D hu))

private theorem coordinates_tmul (D : LatticeData) (hu : IsUnit D.G.det)
    (p : Oscillator D) (g : ActualGround D hu) (b : Half (groundRank D hu)) :
    coordinates D hu (p ⊗ₜ[ℂ] g) b = g b • p := by
  simp only [coordinates, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

/-- This is a coordinate identity, not an assertion of projection stability. -/
private theorem coordinates_tensorEnd (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (Oscillator D)) (v : ActualTensor D hu)
    (b : Half (groundRank D hu)) :
    coordinates D hu (LatticeHalfFock.tensorEnd D (ActualGround D hu) A v) b =
      A (coordinates D hu v b) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul p g =>
    simp only [LatticeHalfFock.tensorEnd, TensorProduct.map_tmul,
      LinearMap.id_apply, coordinates_tmul, map_smul]
  | add v w hv hw =>
    simp only [map_add, Pi.add_apply, hv, hw]

private def partialEnd (D : LatticeData) (hu : IsUnit D.G.det) (x : Index D) :
    Module.End ℂ (ActualTensor D hu) :=
  LatticeHalfFock.tensorEnd D (ActualGround D hu) (pderiv x).toLinearMap

private theorem coordinates_partialEnd (D : LatticeData) (hu : IsUnit D.G.det)
    (x : Index D) (v : ActualTensor D hu) (b : Half (groundRank D hu)) :
    coordinates D hu (partialEnd D hu x v) b =
      pderiv x (coordinates D hu v b) := by
  exact coordinates_tensorEnd D hu (pderiv x).toLinearMap v b

private def delta (D : LatticeData) (hu : IsUnit D.G.det)
    (v : ActualTensor D hu) : ℕ :=
  Finset.univ.sup (fun b : Half (groundRank D hu) =>
    (coordinates D hu v b).totalDegree)

/-- The simultaneous finite-coordinate step missing from scalar descent.
No ground-coordinate projection is applied to the invariant submodule. -/
private theorem delta_partialEnd_lt (D : LatticeData) (hu : IsUnit D.G.det)
    (x : Index D) (v : ActualTensor D hu) (hne : partialEnd D hu x v ≠ 0) :
    delta D hu (partialEnd D hu x v) < delta D hu v := by
  classical
  obtain ⟨b₀, hb₀⟩ : ∃ b : Half (groundRank D hu),
      pderiv x (coordinates D hu v b) ≠ 0 := by
    by_contra! hz
    apply hne
    apply (coordinates D hu).injective
    funext b
    rw [coordinates_partialEnd]
    simpa only [map_zero, Pi.zero_apply] using hz b
  have hbase := totalDegree_pderiv_lt (coordinates D hu v b₀) x hb₀
  have hbound : (coordinates D hu v b₀).totalDegree ≤ delta D hu v :=
    Finset.le_sup (f := fun b : Half (groundRank D hu) =>
      (coordinates D hu v b).totalDegree) (Finset.mem_univ b₀)
  have hpositive : 0 < delta D hu v :=
    (Nat.zero_le _).trans_lt (hbase.trans_le hbound)
  change (Finset.univ.sup (fun b : Half (groundRank D hu) =>
    (coordinates D hu (partialEnd D hu x v) b).totalDegree)) < delta D hu v
  apply (Finset.sup_lt_iff hpositive).2
  intro b _
  rw [coordinates_partialEnd]
  by_cases hb : pderiv x (coordinates D hu v b) = 0
  · simpa only [hb, MvPolynomial.totalDegree_zero] using hpositive
  · exact (totalDegree_pderiv_lt (coordinates D hu v b) x hb).trans_le
      (Finset.le_sup (f := fun b : Half (groundRank D hu) =>
        (coordinates D hu v b).totalDegree) (Finset.mem_univ b))

/-- The exact actual-tensor extraction, first expressed with the derived partial action.
This helper is consumed below by the original-current statement. -/
private theorem ground_intersection_of_partials
    (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu)) (hS : S ≠ ⊥)
    (hpartial : ∀ (x : Index D) (v : ActualTensor D hu),
      v ∈ S → partialEnd D hu x v ∈ S) :
    ∃ g : ActualGround D hu, g ≠ 0 ∧ ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ S := by
  classical
  obtain ⟨v, hvS, hvne⟩ := S.ne_bot_iff.mp hS
  have hex : ∃ n : ℕ, ∃ w : ActualTensor D hu,
      w ∈ S ∧ w ≠ 0 ∧ delta D hu w = n :=
    ⟨delta D hu v, v, hvS, hvne, rfl⟩
  obtain ⟨w, hwS, hwne, hwdegree⟩ := Nat.find_spec hex
  have hmin (r : ActualTensor D hu) (hr : r ∈ S) (hrne : r ≠ 0) :
      delta D hu w ≤ delta D hu r := by
    rw [hwdegree]
    exact Nat.find_min' hex ⟨r, hr, hrne, rfl⟩
  have hzero (x : Index D) : partialEnd D hu x w = 0 := by
    by_contra hx
    exact (not_le_of_gt (delta_partialEnd_lt D hu x w hx))
      (hmin _ (hpartial x w hwS) hx)
  have hconstant (b : Half (groundRank D hu)) :
      coordinates D hu w b = C (constantCoeff (coordinates D hu w b)) := by
    apply eq_constant_of_partials_zero
    intro x
    rw [← coordinates_partialEnd, hzero x]
    simp
  let g : ActualGround D hu := fun b => constantCoeff (coordinates D hu w b)
  have hw : w = (1 : Oscillator D) ⊗ₜ[ℂ] g := by
    apply (coordinates D hu).injective
    funext b
    rw [coordinates_tmul, hconstant b]
    simp only [g, smul_eq_C_mul, mul_one]
  have hg : g ≠ 0 := by
    intro hz
    apply hwne
    rw [hw, hz, TensorProduct.tmul_zero]
  exact ⟨g, hg, hw ▸ hwS⟩

/-- Nonnegative actual currents imply every individual tensor partial preserves S.
The row of the inverse matrix is H x.1 i (not H i x.1). -/
private theorem partialEnd_mem_of_currents
    (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu))
    (hpos : ∀ (i : Fin D.rank) (k : ℕ) (v : ActualTensor D hu),
      v ∈ S → LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (k : ℤ) v ∈ S)
    (x : Index D) (v : ActualTensor D hu) (hv : v ∈ S) :
    partialEnd D hu x v ∈ S := by
  classical
  let H : Matrix (Fin D.rank) (Fin D.rank) ℂ := (D.G⁻¹).map (Int.castRingHom ℂ)
  have hHG : H * LatticeHalfFock.gramComplex D = 1 := by
    have hm := congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℤ =>
      M.map (Int.castRingHom ℂ)) (Matrix.nonsing_inv_mul D.G hu)
    change (D.G⁻¹.map (Int.castRingHom ℂ)) * (D.G.map (Int.castRingHom ℂ)) = 1
    rw [← Matrix.map_mul]
    simpa using hm
  have hf : LatticeHalfFock.frequency (x.2 : ℤ) ≠ 0 := by
    have hscale : (2 : ℂ) * LatticeHalfFock.frequency (x.2 : ℤ) =
        ((2 * x.2 + 1 : ℕ) : ℂ) := by
      simp only [LatticeHalfFock.frequency, Int.cast_natCast]
      push_cast
      ring
    intro hz
    have hn : 2 * x.2 + 1 = 0 := by
      have hc : ((2 * x.2 + 1 : ℕ) : ℂ) = 0 := by rw [← hscale, hz, mul_zero]
      exact_mod_cast hc
    omega
  have hcurrent (i : Fin D.rank) :
      LatticeHalfFock.current D i (x.2 : ℤ) =
        LatticeHalfFock.frequency (x.2 : ℤ) • weightedPartial D i x.2 := by
    simp [LatticeHalfFock.current, LatticeActualAnnihilation.annihilate,
      show ¬ (x.2 : ℤ) < 0 by omega]
  have hweighted (i : Fin D.rank) :
      LatticeHalfFock.tensorEnd D (ActualGround D hu) (weightedPartial D i x.2) v ∈ S := by
    have hs := S.smul_mem (LatticeHalfFock.frequency (x.2 : ℤ))⁻¹ (hpos i x.2 v hv)
    have ht : LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (x.2 : ℤ) v =
        LatticeHalfFock.frequency (x.2 : ℤ) •
          LatticeHalfFock.tensorEnd D (ActualGround D hu) (weightedPartial D i x.2) v := by
      change (LatticeHalfFock.tensorEndLinear D (ActualGround D hu))
        (LatticeHalfFock.current D i (x.2 : ℤ)) v = _
      simp only [hcurrent, map_smul, LinearMap.smul_apply]
      rfl
    rw [ht, smul_smul, inv_mul_cancel₀ hf, one_smul] at hs
    exact hs
  have reconstruct : (∑ i : Fin D.rank, H x.1 i • weightedPartial D i x.2) =
      (pderiv x).toLinearMap := by
    apply LinearMap.ext
    intro p
    simp only [weightedPartial, LinearMap.sum_apply, LinearMap.smul_apply,
      Derivation.coeFn_coe, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have row (j : Fin D.rank) : ∑ i, H x.1 i * (D.G i j : ℂ) =
        if x.1 = j then 1 else 0 := by
      simpa [Matrix.mul_apply, LatticeHalfFock.gramComplex, Matrix.one_apply] using
        congrArg (fun M : Matrix (Fin D.rank) (Fin D.rank) ℂ => M x.1 j) hHG
    simp_rw [row]
    simp
  have transported : partialEnd D hu x v =
      ∑ i : Fin D.rank, H x.1 i •
        LatticeHalfFock.tensorEnd D (ActualGround D hu) (weightedPartial D i x.2) v := by
    change (LatticeHalfFock.tensorEndLinear D (ActualGround D hu))
      (pderiv x).toLinearMap v = _
    rw [← reconstruct, map_sum]
    simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  rw [transported]
  exact S.sum_mem fun i _ => S.smul_mem _ (hweighted i)

/-- Nonnegative actual currents extract a nonzero actual ground vector. -/
theorem nonzero_current_stable_submodule_meets_ground
    (D : LatticeData) (hu : IsUnit D.G.det)
    (S : Submodule ℂ (ActualTensor D hu)) (hS : S ≠ ⊥)
    (hpos : ∀ (i : Fin D.rank) (k : ℕ) (v : ActualTensor D hu),
      v ∈ S → LatticeHalfFock.tensorCurrent D (ActualGround D hu) i (k : ℤ) v ∈ S) :
    ∃ g : ActualGround D hu, g ≠ 0 ∧ ((1 : Oscillator D) ⊗ₜ[ℂ] g) ∈ S := by
  exact ground_intersection_of_partials D hu S hS
    (partialEnd_mem_of_currents D hu S hpos)

end D5.S3.VertexAlgebra.ActualTensorGroundIntersection
