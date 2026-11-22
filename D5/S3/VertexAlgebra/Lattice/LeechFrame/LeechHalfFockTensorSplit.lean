/- GID: D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockTensorSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Tensor splitting into the selected Leech frame coordinate and its complement. -/

import D5.S3.VertexAlgebra.Lattice.LeechFrame.LeechOrthogonalHalfFockCurrents
import D5.S3.VertexAlgebra.LatticeHalfFockParityT
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Module

/-! Splitting the actual Leech half-Fock oscillator polynomials at one frame coordinate. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechHalfFockTensorSplit

open ActualLeechHyperbolic (leechData)
open ActualLeechNormFourFrame (Index)
open ActualLeechHalfFockCurrents (orthonormalBasis)
open LatticeLightConeCoordinates (PolynomialCoordinates polynomialEquiv)
open LatticeGeneratingFieldLocality (Oscillator)
open LatticeHalfFock (coordinateCurrent polarizedCurrent)
open MvPolynomial
open scoped TensorProduct

abbrev Complement (c : Index) := {d : Index // d ≠ c}
abbrev SinglePolynomial := MvPolynomial ℕ ℂ
abbrev ComplementPolynomial (c : Index) := PolynomialCoordinates (Complement c)
abbrev SplitPolynomial (c : Index) := SinglePolynomial ⊗[ℂ] ComplementPolynomial c

variable (c : Index)

def singleVar (k : ℕ) : Index × ℕ := (c, k)

def complementVar (x : Complement c × ℕ) : Index × ℕ := (x.1.val, x.2)

/-- Separate the variables of the chosen coordinate from the other variables. -/
def variableSplit : (Index × ℕ) ≃ (ℕ ⊕ (Complement c × ℕ)) where
  toFun x := if h : x.1 = c then .inl x.2 else .inr (⟨x.1, h⟩, x.2)
  invFun := Sum.elim (singleVar c) (complementVar c)
  left_inv := by
    rintro ⟨d, k⟩
    by_cases h : d = c
    · subst d
      simp [singleVar]
    · simp [h, complementVar]
  right_inv := by
    rintro (k | ⟨d, k⟩)
    · simp [singleVar]
    · simp [complementVar, d.property]

/-- The inverse of the splitting, implemented by Mathlib's polynomial tensor
equivalence followed by renaming. -/
def join : SplitPolynomial c ≃ₐ[ℂ] PolynomialCoordinates Index :=
  (tensorEquivSum ℂ ℕ (Complement c × ℕ) ℂ).trans (renameEquiv ℂ (variableSplit c).symm)

/-- The polynomial tensor splitting in the orthonormal frame. -/
def split : PolynomialCoordinates Index ≃ₐ[ℂ] SplitPolynomial c :=
  (join c).symm

/-- The complete change of representation from the native Leech oscillators. -/
def nativeSplit : Oscillator leechData ≃ₐ[ℂ] SplitPolynomial c :=
  (polynomialEquiv orthonormalBasis).trans (split c)

@[simp] theorem join_X_tmul_one (k : ℕ) :
    join c (X k ⊗ₜ[ℂ] 1) = X (c, k) := by
  simp [join, singleVar, variableSplit]

@[simp] theorem join_one_tmul_X (d : Complement c) (k : ℕ) :
    join c (1 ⊗ₜ[ℂ] X (d, k)) = X (d.val, k) := by
  simp [join, complementVar, variableSplit]

@[simp] theorem split_X_single (k : ℕ) :
    split c (X (c, k)) = X k ⊗ₜ[ℂ] 1 :=
  (join c).symm_apply_eq.mpr (join_X_tmul_one c k).symm

@[simp] theorem split_X_complement (d : Complement c) (k : ℕ) :
    split c (X (d.val, k)) = 1 ⊗ₜ[ℂ] X (d, k) :=
  (join c).symm_apply_eq.mpr (join_one_tmul_X c d k).symm

private theorem join_tmul_one (P : SinglePolynomial) :
    join c (P ⊗ₜ[ℂ] 1) = rename (singleVar c) P := by
  have h : (join c).toAlgHom.comp Algebra.TensorProduct.includeLeft =
      rename (R := ℂ) (singleVar c) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [singleVar]
  exact DFunLike.congr_fun h P

private theorem join_one_tmul (R : ComplementPolynomial c) :
    join c (1 ⊗ₜ[ℂ] R) = rename (complementVar c) R := by
  have h : (join c).toAlgHom.comp Algebra.TensorProduct.includeRight =
      rename (R := ℂ) (complementVar c) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨d, k⟩
    simp [complementVar]
  exact DFunLike.congr_fun h R

theorem join_tmul (P : SinglePolynomial) (R : ComplementPolynomial c) :
    join c (P ⊗ₜ[ℂ] R) = rename (singleVar c) P * rename (complementVar c) R := by
  rw [← join_tmul_one, ← join_one_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- A half-integral oscillator current whose mode m has frequency m + 1/2.
The variable at index k creates at mode -k-1 and is differentiated at mode k. -/
def oscillatorMode {σ : Type*} (x : ℕ → σ) : ℤ → Module.End ℂ (MvPolynomial σ ℂ)
  | .ofNat k => (k + 1 / 2 : ℂ) • (pderiv (x k)).toLinearMap
  | .negSucc k => LinearMap.mulLeft ℂ (X (x k))

abbrev singleCurrent : ℤ → Module.End ℂ SinglePolynomial :=
  oscillatorMode id

abbrev complementCurrent {c : Index} (d : Complement c) :
    ℤ → Module.End ℂ (ComplementPolynomial c) :=
  oscillatorMode (fun k => (d, k))

theorem coordinateCurrent_eq_oscillatorMode (d : Index) (m : ℤ) :
    coordinateCurrent orthonormalBasis d m = oscillatorMode (singleVar d) m := by
  cases m with
  | ofNat k => exact ActualLeechHalfFockCurrents.current_nonnegative d k
  | negSucc k =>
    change coordinateCurrent orthonormalBasis d (Int.negSucc k) = LinearMap.mulLeft ℂ (X (d, k))
    rw [show Int.negSucc k = -(k : ℤ) - 1 by omega]
    exact ActualLeechHalfFockCurrents.current_negative d k

private theorem oscillatorMode_rename {σ τ : Type*} (f : σ → τ) (hf : Function.Injective f)
    (x : ℕ → σ) (m : ℤ) (P : MvPolynomial σ ℂ) :
    oscillatorMode (f ∘ x) m (rename f P) = rename f (oscillatorMode x m P) := by
  cases m with
  | ofNat k =>
    simp [oscillatorMode, pderiv_rename hf]
  | negSucc k =>
    simp [oscillatorMode]

private theorem singleVar_injective : Function.Injective (singleVar c) :=
  fun _ _ h => congrArg Prod.snd h

private theorem complementVar_injective : Function.Injective (complementVar c) := by
  rintro ⟨d, k⟩ ⟨e, l⟩ h
  change (d.val, k) = (e.val, l) at h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (Prod.snd : Index × ℕ → ℕ) h)

private theorem notMem_complement_vars (R : ComplementPolynomial c) (k : ℕ) :
    (c, k) ∉ (rename (R := ℂ) (complementVar c) R).vars := by
  intro h
  obtain ⟨⟨d, l⟩, _, hl⟩ := mem_vars_rename (complementVar c) R h
  exact d.property (congrArg Prod.fst hl)

private theorem notMem_single_vars (d : Complement c) (P : SinglePolynomial) (k : ℕ) :
    (d.val, k) ∉ (rename (R := ℂ) (singleVar c) P).vars := by
  intro h
  obtain ⟨l, _, hl⟩ := mem_vars_rename (singleVar c) P h
  exact d.property (congrArg Prod.fst hl).symm

theorem current_join_tmul_single (m : ℤ) (P : SinglePolynomial) (R : ComplementPolynomial c) :
    coordinateCurrent orthonormalBasis c m (join c (P ⊗ₜ[ℂ] R)) =
      join c (singleCurrent m P ⊗ₜ[ℂ] R) := by
  rw [join_tmul, join_tmul, ActualLeechHalfFockCurrents.current_mul_of_notMem_vars
    c m _ _ (notMem_complement_vars c R), coordinateCurrent_eq_oscillatorMode]
  exact congrArg (· * rename (complementVar c) R)
    (oscillatorMode_rename (singleVar c) (singleVar_injective c) id m P)

theorem current_join_tmul_complement (d : Complement c) (m : ℤ)
    (P : SinglePolynomial) (R : ComplementPolynomial c) :
    coordinateCurrent orthonormalBasis d.val m (join c (P ⊗ₜ[ℂ] R)) =
      join c (P ⊗ₜ[ℂ] complementCurrent d m R) := by
  rw [join_tmul, join_tmul, mul_comm (rename (singleVar c) P),
    ActualLeechHalfFockCurrents.current_mul_of_notMem_vars
      d.val m _ _ (notMem_single_vars c d P), coordinateCurrent_eq_oscillatorMode,
    mul_comm _ (rename (singleVar c) P)]
  exact congrArg (rename (singleVar c) P * ·)
    (oscillatorMode_rename (complementVar c) (complementVar_injective c) (fun k => (d, k)) m R)

theorem split_coordinateCurrent_single (m : ℤ) :
    (split c).toLinearEquiv.conj (coordinateCurrent orthonormalBasis c m) =
      TensorProduct.map (singleCurrent m) LinearMap.id := by
  apply TensorProduct.ext'
  intro P R
  change split c (coordinateCurrent orthonormalBasis c m (join c (P ⊗ₜ[ℂ] R))) = _
  rw [current_join_tmul_single, TensorProduct.map_tmul, LinearMap.id_apply]
  exact (join c).symm_apply_apply _

theorem split_coordinateCurrent_complement (d : Complement c) (m : ℤ) :
    (split c).toLinearEquiv.conj (coordinateCurrent orthonormalBasis d.val m) =
      TensorProduct.map LinearMap.id (complementCurrent d m) := by
  apply TensorProduct.ext'
  intro P R
  change split c (coordinateCurrent orthonormalBasis d.val m (join c (P ⊗ₜ[ℂ] R))) = _
  rw [current_join_tmul_complement, TensorProduct.map_tmul, LinearMap.id_apply]
  exact (join c).symm_apply_apply _

/-- Every native mode polarized by the chosen unit vector acts on the single
factor, including the positive-frequency mode indexed by zero. -/
theorem nativeSplit_current_single (m : ℤ) :
    (nativeSplit c).toLinearEquiv.conj (polarizedCurrent m (orthonormalBasis c)) =
      TensorProduct.map (singleCurrent m) LinearMap.id :=
  split_coordinateCurrent_single c m

/-- Each other orthonormal-frame current acts on its coordinate in the complement. -/
theorem nativeSplit_current_complement (d : Complement c) (m : ℤ) :
    (nativeSplit c).toLinearEquiv.conj (polarizedCurrent m (orthonormalBasis d.val)) =
      TensorProduct.map LinearMap.id (complementCurrent d m) :=
  split_coordinateCurrent_complement c d m

/-- The simultaneous sign change of all polynomial variables. -/
def polynomialSign (σ : Type*) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval (fun i => -X i)

@[simp] theorem polynomialSign_X {σ : Type*} (i : σ) :
    polynomialSign σ (X i) = -X i :=
  aeval_X _ _

theorem polynomialSign_involutive (σ : Type*) : Function.Involutive (polynomialSign σ) := by
  have h : (polynomialSign σ).comp (polynomialSign σ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact DFunLike.congr_fun h

private theorem polynomialSign_rename {σ τ : Type*} (f : σ → τ) (P : MvPolynomial σ ℂ) :
    polynomialSign τ (rename f P) = rename f (polynomialSign σ P) := by
  have h : (polynomialSign τ).comp (rename f) = (rename f).comp (polynomialSign σ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact DFunLike.congr_fun h P

abbrev splitParity : Module.End ℂ (SplitPolynomial c) :=
  TensorProduct.map (polynomialSign ℕ).toLinearMap (polynomialSign (Complement c × ℕ)).toLinearMap

theorem split_polynomialSign :
    (split c).toLinearEquiv.conj (polynomialSign (Index × ℕ)).toLinearMap = splitParity c := by
  apply TensorProduct.ext'
  intro P R
  have h : polynomialSign (Index × ℕ) (join c (P ⊗ₜ[ℂ] R)) =
      join c (polynomialSign ℕ P ⊗ₜ[ℂ] polynomialSign (Complement c × ℕ) R) := by
    rw [join_tmul, join_tmul, map_mul, polynomialSign_rename, polynomialSign_rename]
  change split c (polynomialSign _ (join c (P ⊗ₜ[ℂ] R))) =
    polynomialSign ℕ P ⊗ₜ[ℂ] polynomialSign (Complement c × ℕ) R
  rw [h]
  exact (join c).symm_apply_apply _

open LatticeInvolution (sigmaLinear)

set_option backward.isDefEq.respectTransparency false in
theorem orthonormal_coordinates_sigma :
    (polynomialEquiv orthonormalBasis).toLinearEquiv.conj (sigmaLinear leechData) =
      (polynomialSign (Index × ℕ)).toLinearMap := by
  let e := polynomialEquiv orthonormalBasis
  have h : (polynomialSign _).comp e.symm.toAlgHom =
      e.symm.toAlgHom.comp (polynomialSign (Index × ℕ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨d, k⟩
    have hx : e.symm (X (d, k)) = LatticeLightConeCoordinates.lin k (orthonormalBasis d) :=
      aeval_X (fun x : Index × ℕ => LatticeLightConeCoordinates.lin x.2 (orthonormalBasis x.1)) (d, k)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, polynomialSign_X, map_neg, hx]
    simp [LatticeLightConeCoordinates.lin, map_sum, Finset.sum_neg_distrib]
  apply LinearMap.ext
  intro Q
  apply e.symm.injective
  have hs (P : Oscillator leechData) : sigmaLinear leechData P = polynomialSign _ P := rfl
  change e.symm (e (sigmaLinear leechData (e.symm Q))) = e.symm (polynomialSign _ Q)
  rw [AlgEquiv.symm_apply_apply, hs]
  exact DFunLike.congr_fun h Q

theorem nativeSplit_sigma :
    (nativeSplit c).toLinearEquiv.conj (sigmaLinear leechData) = splitParity c := by
  change ((polynomialEquiv orthonormalBasis).toLinearEquiv.trans
    (split c).toLinearEquiv).conj _ = _
  rw [← LinearEquiv.conj_trans]
  change (split c).toLinearEquiv.conj
    ((polynomialEquiv orthonormalBasis).toLinearEquiv.conj (sigmaLinear leechData)) = _
  rw [orthonormal_coordinates_sigma, split_polynomialSign]

open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor)
open LatticeHalfFockParityT (actualParity)

/-- The oscillator splitting on the actual twisted tensor module with its
ground representation carried along unchanged. -/
def nativeTensorSplit (hu : IsUnit leechData.G.det) :
    ActualTensor leechData hu ≃ₗ[ℂ] SplitPolynomial c ⊗[ℂ] ActualGround leechData hu :=
  TensorProduct.congr (nativeSplit c).toLinearEquiv (LinearEquiv.refl ℂ _)

theorem nativeTensorSplit_actualParity (hu : IsUnit leechData.G.det) :
    (nativeTensorSplit c hu).conj (actualParity leechData hu) =
      TensorProduct.map (splitParity c) LinearMap.id := by
  apply TensorProduct.ext'
  intro P R
  change nativeSplit c (sigmaLinear leechData ((nativeSplit c).symm P)) ⊗ₜ[ℂ] R =
    splitParity c P ⊗ₜ[ℂ] R
  exact congrArg (· ⊗ₜ[ℂ] R) (LinearMap.congr_fun (nativeSplit_sigma c) P)

section TensorEigenspaces

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

open Module.End (eigenspace mem_eigenspace_iff)

private def signedSum (A : Module.End ℂ M) (a : ℂ) : Module.End ℂ M :=
  LinearMap.id + a • A

private theorem signedSum_mem (A : Module.End ℂ M) (hA : Function.Involutive A)
    (a : ℂ) (ha : a * a = 1) (x : M) : signedSum A a x ∈ eigenspace A a := by
  rw [mem_eigenspace_iff]
  simp only [signedSum, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
    map_add, map_smul, hA x, smul_add, smul_smul, ha, one_smul]
  exact add_comm _ _

private theorem range_signedSum (A : Module.End ℂ M) (hA : Function.Involutive A)
    (a : ℂ) (ha : a * a = 1) : LinearMap.range (signedSum A a) = eigenspace A a := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact signedSum_mem A hA a ha x
  · intro x hx
    have hAx := mem_eigenspace_iff.mp hx
    refine ⟨(1 / 2 : ℂ) • x, ?_⟩
    rw [map_smul]
    simp only [signedSum, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
      hAx, smul_smul, ha, one_smul]
    module

/-- The subspace spanned by tensors of the two indicated parity eigenspaces. -/
def tensorParitySector (A : Module.End ℂ M) (B : Module.End ℂ N) (a b : ℂ) :
    Submodule ℂ (M ⊗[ℂ] N) :=
  Submodule.map₂ (TensorProduct.mk ℂ M N) (eigenspace A a) (eigenspace B b)

private theorem range_tensorSignedSum (A : Module.End ℂ M) (B : Module.End ℂ N)
    (hA : Function.Involutive A) (hB : Function.Involutive B)
    (a b : ℂ) (ha : a * a = 1) (hb : b * b = 1) :
    LinearMap.range (TensorProduct.map (signedSum A a) (signedSum B b)) =
      tensorParitySector A B a b := by
  rw [TensorProduct.range_map, range_signedSum A hA a ha, range_signedSum B hB b hb]
  rfl

private theorem tensorParitySector_le (A : Module.End ℂ M) (B : Module.End ℂ N) (a b : ℂ) :
    tensorParitySector A B a b ≤ eigenspace (TensorProduct.map A B) (a * b) := by
  rw [tensorParitySector, Submodule.map₂_le]
  intro p hp q hq
  rw [mem_eigenspace_iff, TensorProduct.mk_apply, TensorProduct.map_tmul,
    mem_eigenspace_iff.mp hp, mem_eigenspace_iff.mp hq, TensorProduct.smul_tmul_smul]

private theorem tensorParitySector_le_left (A : Module.End ℂ M) (B : Module.End ℂ N)
    (a b : ℂ) :
    tensorParitySector A B a b ≤ eigenspace (TensorProduct.map A (LinearMap.id : Module.End ℂ N)) a := by
  rw [tensorParitySector, Submodule.map₂_le]
  intro p hp q _
  rw [mem_eigenspace_iff, TensorProduct.mk_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    mem_eigenspace_iff.mp hp, ← TensorProduct.smul_tmul']

/-- Different eigenvalues of the first factor give disjoint tensor sectors. -/
theorem tensorParitySector_disjoint_left (A : Module.End ℂ M) (B : Module.End ℂ N)
    {a a' : ℂ} (h : a ≠ a') (b b' : ℂ) :
    Disjoint (tensorParitySector A B a b) (tensorParitySector A B a' b') :=
  ((Module.End.eigenspaces_iSupIndep
    (TensorProduct.map A (LinearMap.id : Module.End ℂ N))).pairwiseDisjoint h).mono
      (tensorParitySector_le_left A B a b) (tensorParitySector_le_left A B a' b')

private theorem tensorSignedSum_add (A : Module.End ℂ M) (B : Module.End ℂ N) (s : ℂ) :
    TensorProduct.map (signedSum A 1) (signedSum B s) +
      TensorProduct.map (signedSum A (-1)) (signedSum B (-s)) =
        (2 : ℂ) • signedSum (TensorProduct.map A B) s := by
  simp only [signedSum, TensorProduct.map_add_left, TensorProduct.map_add_right,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right, TensorProduct.map_id]
  module

private theorem eigenspace_tensorParity (A : Module.End ℂ M) (B : Module.End ℂ N)
    (hA : Function.Involutive A) (hB : Function.Involutive B)
    (s : ℂ) (hs : s * s = 1) :
    eigenspace (TensorProduct.map A B) s =
      tensorParitySector A B 1 s ⊔ tensorParitySector A B (-1) (-s) := by
  have hneg : (-s) * (-s) = 1 := by simpa using hs
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · have hRange := LinearMap.range_add_le
      (TensorProduct.map (signedSum A 1) (signedSum B s))
      (TensorProduct.map (signedSum A (-1)) (signedSum B (-s)))
    rw [tensorSignedSum_add, range_tensorSignedSum A B hA hB 1 s (by norm_num) hs,
      range_tensorSignedSum A B hA hB (-1) (-s) (by norm_num) hneg] at hRange
    intro x hx
    apply hRange
    refine ⟨(1 / 4 : ℂ) • x, ?_⟩
    rw [map_smul]
    simp only [signedSum, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      mem_eigenspace_iff.mp hx, smul_smul, hs, one_smul]
    module
  · simpa only [one_mul] using tensorParitySector_le A B 1 s
  · simpa only [neg_mul_neg, one_mul] using
      tensorParitySector_le A B (-1) (-s)

end TensorEigenspaces

/-- In the split polynomial representation, resolve parity in each factor. -/
abbrev coordinateParitySector (a b : ℂ) : Submodule ℂ (SplitPolynomial c) :=
  tensorParitySector (polynomialSign ℕ).toLinearMap
    (polynomialSign (Complement c × ℕ)).toLinearMap a b

/-- The positive oscillator sector consists of the two matching parity sectors. -/
theorem splitParity_eigenspace_pos :
    Module.End.eigenspace (splitParity c) 1 =
      coordinateParitySector c 1 1 ⊔ coordinateParitySector c (-1) (-1) := by
  exact eigenspace_tensorParity _ _ (polynomialSign_involutive ℕ)
    (polynomialSign_involutive (Complement c × ℕ)) 1 (by norm_num)

/-- The negative oscillator sector consists of the two opposite parity sectors. -/
theorem splitParity_eigenspace_neg :
    Module.End.eigenspace (splitParity c) (-1) =
      coordinateParitySector c 1 (-1) ⊔ coordinateParitySector c (-1) 1 := by
  simpa only [neg_neg] using eigenspace_tensorParity _ _ (polynomialSign_involutive ℕ)
    (polynomialSign_involutive (Complement c × ℕ)) (-1) (by norm_num)

end D5.S3.VertexAlgebra.ActualLeechHalfFockTensorSplit
