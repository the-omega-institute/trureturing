/- GID: D5/S3/VertexAlgebra/LatticeHalfFockTensorFields
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockTensorFields
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual half-integer lattice currents, finite normal sums and Virasoro fields. -/

/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Additional actual half-integer matrix implementation copyright (c) 2026.
Released under Apache 2.0.
Finite support, contraction and induction architecture adapted from
VirasoroProject 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 through the completed
trureturing PolynomialFock sources at bfd9ff0f15397a4fb933f36d701a60d325d84b08.
Actual multicolour half-index operators and their proofs are retained from the
completed half-Fock producer; see notes/NOTICE.md and DeclarationMapping.json.
DN math/9808088v1, section 3.2, pp.12--14; rank/16 on p.19, proof of 3.13(3),
attributed there to FLM. BK math/0402315v1 (4.4), pp.10--13 (4.23)--(4.38).
-/
import D5.S3.VertexAlgebra.LatticeHalfFockVirasoroSpectrum

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFock
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration MvPolynomial
open LatticeActualAnnihilation
open scoped BigOperators TensorProduct
noncomputable section

def tensorEnd (D : LatticeData) (T : Type*) [AddCommGroup T] [Module ℂ T]
    (A : Module.End ℂ (Oscillator D)) :
    Module.End ℂ (Oscillator D ⊗[ℂ] T) := TensorProduct.map A LinearMap.id

@[simp] private theorem tensorEnd_tmul (D : LatticeData) (T : Type*)
    [AddCommGroup T] [Module ℂ T] (A : Module.End ℂ (Oscillator D))
    (p : Oscillator D) (t : T) : tensorEnd D T A (p ⊗ₜ[ℂ] t) = A p ⊗ₜ[ℂ] t := by
  simp [tensorEnd]

def tensorCurrent (D : LatticeData) (T : Type*) [AddCommGroup T] [Module ℂ T]
    (i : Fin D.rank) (j : ℤ) := tensorEnd D T (current D i j)

theorem tensor_current_truncation (D : LatticeData) (T : Type*)
    [AddCommGroup T] [Module ℂ T] (v : Oscillator D ⊗[ℂ] T) :
    ∃ R : ℕ, ∀ (i : Fin D.rank) (j : ℤ), (R : ℤ) ≤ j → tensorCurrent D T i j v = 0 := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, by intros; simp⟩
  | tmul p t =>
    refine ⟨bound D p, ?_⟩
    intro i j hj
    simp [tensorCurrent, current_vanish D i p j hj]
  | add v w hv hw =>
    obtain ⟨R,hR⟩ := hv; obtain ⟨S,hS⟩ := hw
    refine ⟨max R S, ?_⟩
    intro i j hj
    have hr : (R : ℤ) ≤ j := by exact le_trans (by exact_mod_cast le_max_left R S) hj
    have hs : (S : ℤ) ≤ j := by exact le_trans (by exact_mod_cast le_max_right R S) hj
    simp [hR i j hr, hS i j hs]

def currentCoeff (D : LatticeData) (i : Fin D.rank) (e : ℤ) :
    Module.End ℂ (Oscillator D) :=
  if e % 2 = 1 then current D i ((-e-3)/2) else 0

private theorem currentCoeff_bound (D : LatticeData) (i : Fin D.rank) (p : Oscillator D) :
    BddBelow (Function.support (fun e : ℤ => currentCoeff D i e p)) := by
  refine ⟨-2*(bound D p : ℤ)-3, ?_⟩
  intro e he
  by_contra h
  have hzero : currentCoeff D i e p = 0 := by
    unfold currentCoeff
    split_ifs
    · exact current_vanish D i p _ (by omega)
    · simp
  exact he hzero

abbrev HalfField (V : Type*) [AddCommGroup V] [Module ℂ V] :=
  HVertexOperator ℤ ℂ V V

def currentField (D : LatticeData) (i : Fin D.rank) : HalfField (Oscillator D) :=
  HVertexOperator.of_coeff (currentCoeff D i) fun p =>
    (currentCoeff_bound D i p).isWF.isPWO

section Tensor
variable (D : LatticeData) (T : Type*) [AddCommGroup T] [Module ℂ T]

def tensorEndLinear : Module.End ℂ (Oscillator D) →ₗ[ℂ]
    Module.End ℂ (Oscillator D ⊗[ℂ] T) where
  toFun := tensorEnd D T
  map_add' A B := by
    apply TensorProduct.ext'; intro p t
    simp [tensorEnd_tmul, TensorProduct.add_tmul]
  map_smul' c A := by
    apply TensorProduct.ext'; intro p t
    simp [tensorEnd_tmul, TensorProduct.smul_tmul]

private theorem tensorEnd_mul (A B : Module.End ℂ (Oscillator D)) :
    tensorEnd D T (A*B) = tensorEnd D T A*tensorEnd D T B := by
  apply TensorProduct.ext'; intro p t
  simp [Module.End.mul_apply]

def tensorL (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) := tensorEnd D T (L D H m)

def tensorRawL (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) := tensorEnd D T (rawL D H m)

def tensorPair (i l : Fin D.rank) (j k : ℤ) := tensorEnd D T (normalPair D i l j k)

private theorem tensorPair_eq (i l : Fin D.rank) (j k : ℤ) :
    tensorPair D T i l j k =
      if j < 0 then tensorCurrent D T i j*tensorCurrent D T l k
      else tensorCurrent D T l k*tensorCurrent D T i j := by
  unfold tensorPair normalPair
  split_ifs <;> exact tensorEnd_mul D T _ _

theorem tensorPair_support_of_bound (i l : Fin D.rank) (m : ℤ)
    (v : Oscillator D ⊗[ℂ] T) (R : ℕ)
    (hR : ∀ (a : Fin D.rank) (j : ℤ), (R : ℤ) ≤ j → tensorCurrent D T a j v = 0) :
    Function.support (fun j : ℤ => tensorPair D T i l j (m-j-1) v) ⊆
      Set.Icc (min (m-R) 0) ((R : ℤ)-1) := by
  intro j hj
  by_contra h
  have ho : j < min (m-R) 0 ∨ (R : ℤ) ≤ j := by
    simp only [Set.mem_Icc, not_and_or, not_le] at h; omega
  rcases ho with hlo | hhi
  · have hneg : j < 0 := lt_of_lt_of_le hlo (min_le_right _ _)
    have hk : (R : ℤ) ≤ m-j-1 := by
      have := lt_of_lt_of_le hlo (min_le_left _ _); omega
    exact hj (by simp [tensorPair_eq, hneg, Module.End.mul_apply, hR l _ hk])
  · exact hj (by simp [tensorPair_eq, show ¬ j < 0 by omega,
      Module.End.mul_apply, hR i _ hhi])

private theorem tensorPair_finite (i l : Fin D.rank) (m : ℤ) (v : Oscillator D ⊗[ℂ] T) :
    Function.HasFiniteSupport (fun j : ℤ => tensorPair D T i l j (m-j-1) v) := by
  obtain ⟨R,hR⟩ := tensor_current_truncation D T v
  exact (Set.finite_Icc _ _).subset (tensorPair_support_of_bound D T i l m v R hR)

def tensorNormalSum (i l : Fin D.rank) (m : ℤ) :
    Module.End ℂ (Oscillator D ⊗[ℂ] T) where
  toFun v := ∑ᶠ j : ℤ, tensorPair D T i l j (m-j-1) v
  map_add' v w := by
    simp only [map_add]
    exact finsum_add_distrib (tensorPair_finite D T i l m v) (tensorPair_finite D T i l m w)
  map_smul' c v := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (tensorPair_finite D T i l m v)).symm

private theorem tensor_normalSum (i l : Fin D.rank) (m : ℤ) :
    tensorEnd D T (normalSum D i l m) = tensorNormalSum D T i l m := by
  apply TensorProduct.ext'; intro p t
  simp only [tensorEnd_tmul]
  change (∑ᶠ j : ℤ, normalPair D i l j (m-j-1) p) ⊗ₜ[ℂ] t =
    ∑ᶠ j : ℤ, tensorEnd D T (normalPair D i l j (m-j-1)) (p ⊗ₜ[ℂ] t)
  simp only [tensorEnd_tmul]
  exact (map_finsum ((TensorProduct.mk ℂ (Oscillator D) T).flip t)
    (normalPair_finite D i l m p))

theorem tensor_rawL_finsum (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (m : ℤ) (v : Oscillator D ⊗[ℂ] T) :
    tensorRawL D T H m v = (2 : ℂ)⁻¹ •
      ∑ i : Fin D.rank, ∑ l : Fin D.rank, H i l •
        ∑ᶠ j : ℤ, tensorPair D T i l j (m-j-1) v := by
  change tensorEndLinear D T (rawL D H m) v = _
  rw [rawL, map_smul]
  simp only [map_sum, map_smul]
  change ((2 : ℂ)⁻¹ • ∑ i : Fin D.rank, ∑ l : Fin D.rank,
    H i l • tensorEnd D T (normalSum D i l m)) v = _
  simp only [tensor_normalSum, LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

theorem tensor_L_truncation (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (v : Oscillator D ⊗[ℂ] T) :
    ∃ R : ℕ, ∀ m : ℤ, (R : ℤ) < m → tensorL D T H m v = 0 := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, by intros; simp⟩
  | tmul p t =>
    refine ⟨2*bound D p, ?_⟩
    intro m hm
    have hc : 2*(bound D p : ℤ) < m := by exact_mod_cast hm
    simp [tensorL, L_truncation D H p m hc]
  | add v w hv hw =>
    obtain ⟨R,hR⟩ := hv; obtain ⟨S,hS⟩ := hw
    refine ⟨max R S, ?_⟩
    intro m hm
    have hr : (R : ℤ) < m := lt_of_le_of_lt (by exact_mod_cast le_max_left R S) hm
    have hs : (S : ℤ) < m := lt_of_le_of_lt (by exact_mod_cast le_max_right R S) hm
    simp [hR m hr, hS m hs]

def tensorCurrentField (i : Fin D.rank) : HalfField (Oscillator D ⊗[ℂ] T) :=
  HVertexOperator.of_coeff (fun e => tensorEnd D T (currentCoeff D i e)) (by
    intro v
    obtain ⟨R,hR⟩ := tensor_current_truncation D T v
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-2*(R : ℤ)-3, ?_⟩
    intro e he
    by_contra h
    have hz : tensorEnd D T (currentCoeff D i e) v = 0 := by
      unfold currentCoeff
      split_ifs
      · exact hR i _ (by omega)
      · exact congrArg (fun A : Module.End ℂ (Oscillator D ⊗[ℂ] T) => A v)
          (map_zero (tensorEndLinear D T))
    exact he hz)

end Tensor

def stressCoeff (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (e : ℤ) :
    Module.End ℂ (Oscillator D) :=
  if e % 2 = 0 then L D H ((-e-4)/2) else 0

private theorem stressCoeff_bound (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p : Oscillator D) :
    BddBelow (Function.support (fun e : ℤ => stressCoeff D H e p)) := by
  refine ⟨-4*(bound D p : ℤ)-6, ?_⟩
  intro e he
  by_contra h
  have hz : stressCoeff D H e p = 0 := by
    unfold stressCoeff
    split_ifs
    · exact L_truncation D H p _ (by omega)
    · simp
  exact he hz

def stressField (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    HalfField (Oscillator D) :=
  HVertexOperator.of_coeff (stressCoeff D H) fun p => (stressCoeff_bound D H p).isWF.isPWO

def tensorStressField (D : LatticeData) (T : Type*) [AddCommGroup T] [Module ℂ T]
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : HalfField (Oscillator D ⊗[ℂ] T) :=
  HVertexOperator.of_coeff (fun e => tensorEnd D T (stressCoeff D H e)) (by
    intro v
    obtain ⟨R,hR⟩ := tensor_L_truncation D T H v
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-2*(R : ℤ)-4, ?_⟩
    intro e he
    by_contra h
    have hz : tensorEnd D T (stressCoeff D H e) v = 0 := by
      unfold stressCoeff
      split_ifs
      · exact hR _ (by omega)
      · exact congrArg (fun A : Module.End ℂ (Oscillator D ⊗[ℂ] T) => A v)
          (map_zero (tensorEndLinear D T))
    exact he hz)

end
end D5.S3.VertexAlgebra.LatticeHalfFock
