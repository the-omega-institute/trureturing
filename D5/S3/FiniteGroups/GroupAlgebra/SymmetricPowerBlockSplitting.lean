/- GID: D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.TensorPower.Symmetric, mathlib/module/Mathlib.LinearAlgebra.PiTensorProduct.Dual]
   utility: none
   digest: Duals of symmetric tensor multiplication sections split in the genuine symmetric quotient. -/

import D5.S3.FiniteGroups.GroupAlgebra.SymmetricPowerTranslation
import D5.S3.FiniteGroups.GroupAlgebra.BoundedTensorPolarization
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Data.Fintype.Perm

/-!
The quotient in this file is Mathlib's additive-congruence symmetric power.
Only the order of the outer permutation group is inverted. The tensor section
itself need not be invariant under permutations: averaging its dual gives a
retraction on the quotient. The inclusion is the unnormalized ordered
coefficient sum, avoiding an assumed symmetric-power duality identification.

The exact Fin-index quotient requires K : Type in the pinned Mathlib API.
The acting additive group retains an independent universe.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.SymmetricPowerBlockSplitting

open Module ElmerKadrTensorCounterexample ElmerKadrPositiveCriterion
open ElmerKadrTensorCounterexample.SymmetricPowerTranslation
open scoped TensorProduct

universe uE uV uN

variable {K : Type} [Field K]

abbrev Tensor (n : ℕ) (A : Type*) [AddCommGroup A] [Module K A] :=
  ⨂[K] (_ : Fin n), A

section QuotientFunctor

variable {V : Type uV} {N : Type uN}
  [AddCommGroup V] [Module K V] [AddCommGroup N] [Module K N]

/-- Functoriality between different modules on the actual quotient. -/
def symmetricMap (n : ℕ) (f : V →ₗ[K] N) :
    SymmetricPower K (Fin n) V →ₗ[K] SymmetricPower K (Fin n) N :=
  liftSymmetric ((SymmetricPower.tprod K).compLinearMap (fun _ => f)) (by
    intro e v
    exact SymmetricPower.tprod_equiv e (fun j => f (v j)))

@[simp] theorem symmetricMap_tprod (n : ℕ) (f : V →ₗ[K] N) (v : Fin n → V) :
    symmetricMap n f (SymmetricPower.tprod K v) =
      SymmetricPower.tprod K (fun j => f (v j)) :=
  liftSymmetric_tprod _ _ _

def symmetricEquiv (n : ℕ) (e : V ≃ₗ[K] N) :
    SymmetricPower K (Fin n) V ≃ₗ[K] SymmetricPower K (Fin n) N where
  __ := symmetricMap n e.toLinearMap
  invFun := symmetricMap n e.symm.toLinearMap
  left_inv x := by
    have h : (symmetricMap n e.symm.toLinearMap).comp
        (symmetricMap n e.toLinearMap) = LinearMap.id := by
      apply ext_tprod
      intro v
      simp only [LinearMap.comp_apply, symmetricMap_tprod, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.id_apply]
    exact LinearMap.congr_fun h x
  right_inv x := by
    have h : (symmetricMap n e.toLinearMap).comp
        (symmetricMap n e.symm.toLinearMap) = LinearMap.id := by
      apply ext_tprod
      intro v
      simp only [LinearMap.comp_apply, symmetricMap_tprod, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    exact LinearMap.congr_fun h x

def symmetricActionEquiv {E : Type uE} [AddGroup E]
    {ρ : Representation K (Multiplicative E) V}
    {σ : Representation K (Multiplicative E) N} (n : ℕ) (e : ρ.Equiv σ) :
    (action ρ n).Equiv (action σ n) :=
  .mk (symmetricEquiv n e.toLinearEquiv) fun g => by
    apply ext_tprod
    intro v
    simp only [LinearMap.comp_apply, action_tprod, symmetricEquiv, symmetricMap_tprod]
    congr 1
    funext j
    exact LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) (v j)

end QuotientFunctor

section TensorActions

variable {E : Type uE} [AddGroup E] {A : Type} [AddCommGroup A] [Module K A]

def tensorAction (ρ : Representation K (Multiplicative E) A) (n : ℕ) :
    Representation K (Multiplicative E) (Tensor (K := K) n A) where
  toFun g := PiTensorProduct.map (fun _ => ρ g)
  map_one' := by simp only [map_one, PiTensorProduct.map_one]
  map_mul' g h := by simp only [map_mul, PiTensorProduct.map_mul]

@[simp] theorem tensorAction_tprod (ρ : Representation K (Multiplicative E) A)
    (n : ℕ) (g : Multiplicative E) (v : Fin n → A) :
    tensorAction ρ n g (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (fun j => ρ g (v j)) := PiTensorProduct.map_tprod _ _

/-- Prepend one factor using the two universal properties, with no quotient
coordinate model or assumed tensor associativity equivalence. -/
def consTensor (n : ℕ) :
    A ⊗[K] Tensor (K := K) n A →ₗ[K] Tensor (K := K) (n + 1) A :=
  TensorProduct.lift
    ((PiTensorProduct.lift (R := K) (s := fun _ : Fin n => A)
      (E := Tensor (K := K) (n + 1) A)).toLinearMap.comp
      (PiTensorProduct.tprod K (ι := Fin (n + 1)) (s := fun _ => A)).curryLeft)

@[simp] theorem consTensor_tmul_tprod (n : ℕ) (a : A) (v : Fin n → A) :
    consTensor n (a ⊗ₜ[K] PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (Fin.cons a v) := by
  simp only [consTensor, TensorProduct.lift.tmul, LinearMap.comp_apply,
    LinearEquiv.coe_coe, PiTensorProduct.lift.tprod, MultilinearMap.curryLeft_apply]

def consIntertwiner (ρ : Representation K (Multiplicative E) A) (n : ℕ) :
    (ρ.tprod (tensorAction ρ n)).IntertwiningMap (tensorAction ρ (n + 1)) where
  toLinearMap := consTensor n
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change consTensor n
        (TensorProduct.map (ρ g) (tensorAction ρ n g)
          (a ⊗ₜ[K] PiTensorProduct.tprod K v)) =
      tensorAction ρ (n + 1) g (consTensor n (a ⊗ₜ[K] PiTensorProduct.tprod K v))
    rw [TensorProduct.map_tmul, tensorAction_tprod, consTensor_tmul_tprod,
      consTensor_tmul_tprod, tensorAction_tprod]
    congr 1
    funext j
    cases j using Fin.cases <;> rfl

def permutation (n : ℕ) (e : Equiv.Perm (Fin n)) :
    Module.End K (Tensor (K := K) n A) :=
  PiTensorProduct.lift ((PiTensorProduct.tprod K).domDomCongr e)

@[simp] theorem permutation_tprod (n : ℕ) (e : Equiv.Perm (Fin n)) (v : Fin n → A) :
    permutation n e (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (fun j => v (e j)) := PiTensorProduct.lift.tprod _

def quotientIntertwiner (ρ : Representation K (Multiplicative E) A) (n : ℕ) :
    (tensorAction ρ n).IntertwiningMap (action ρ n) where
  toLinearMap := SymmetricPower.mk K (Fin n) A
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, tensorAction_tprod]
    change SymmetricPower.tprod K (fun j => ρ g (v j)) =
      action ρ n g (SymmetricPower.tprod K v)
    rw [action_tprod]

def dualTensorEquiv (ρ : Representation K (Multiplicative E) A)
    (n : ℕ) {I : Type} [Fintype I] (b : Basis I K A) :
    (tensorAction ρ.dual n).Equiv (tensorAction ρ n).dual :=
  .mk (PiTensorProduct.dualDistribEquivOfBasis (fun _ : Fin n => b)) fun g => by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro φ
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change PiTensorProduct.dualDistrib
        (tensorAction ρ.dual n g (PiTensorProduct.tprod K φ))
        (PiTensorProduct.tprod K v) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod K φ)
        (tensorAction ρ n g⁻¹ (PiTensorProduct.tprod K v))
    simp only [tensorAction_tprod, PiTensorProduct.dualDistrib_apply,
      Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]

private theorem pair_permutation (n : ℕ) (e : Equiv.Perm (Fin n))
    (t : Tensor (K := K) n (Dual K A)) (v : Fin n → A) :
    PiTensorProduct.dualDistrib (permutation n e t) (PiTensorProduct.tprod K v) =
      PiTensorProduct.dualDistrib t (PiTensorProduct.tprod K (fun j => v (e.symm j))) := by
  refine PiTensorProduct.induction_on t ?_ ?_
  · intro c φ
    simp only [map_smul, LinearMap.smul_apply, permutation_tprod,
      PiTensorProduct.dualDistrib_apply]
    congr 1
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.prod_comp e (fun j => φ j (v (e.symm j))))
  · intro x y hx hy
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy]

/-- The raw dual of multiplication, followed by the actual quotient map. -/
def coefficientInclusion {B : Type} [AddCommGroup B] [Module K B]
    (ρ : Representation K (Multiplicative E) A) (σ : Representation K (Multiplicative E) B)
    (n : ℕ) {I : Type} [Fintype I] (b : Basis I K A)
    (μ : (tensorAction ρ n).IntertwiningMap σ) :
    σ.dual.IntertwiningMap (action ρ.dual n) :=
  (quotientIntertwiner ρ.dual n).comp
    ((dualTensorEquiv ρ n b).symm.toIntertwiningMap.comp (dualIntertwiner μ))

private def averagedMultilinear {B : Type} [AddCommGroup B] [Module K B]
    {σ : Representation K (Multiplicative E) B}
    {ρ : Representation K (Multiplicative E) A} {n : ℕ}
    (r : (tensorAction ρ n).IntertwiningMap σ) :
    MultilinearMap K (fun _ : Fin n => A) B :=
  (n.factorial : K)⁻¹ • ∑ e : Equiv.Perm (Fin n),
    (r.toLinearMap.compMultilinearMap (PiTensorProduct.tprod K)).domDomCongr e

private theorem averagedMultilinear_symmetric {B : Type} [AddCommGroup B] [Module K B]
    {σ : Representation K (Multiplicative E) B}
    {ρ : Representation K (Multiplicative E) A} {n : ℕ}
    (r : (tensorAction ρ n).IntertwiningMap σ)
    (e : Equiv.Perm (Fin n)) (v : Fin n → A) :
    averagedMultilinear r (fun j => v (e j)) = averagedMultilinear r v := by
  classical
  simp only [averagedMultilinear, MultilinearMap.smul_apply,
    MultilinearMap.sum_apply, MultilinearMap.domDomCongr_apply,
    LinearMap.compMultilinearMap_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft e) _ _ (fun f => rfl)

def quotientAverage {B : Type} [AddCommGroup B] [Module K B]
    {σ : Representation K (Multiplicative E) B}
    {ρ : Representation K (Multiplicative E) A} {n : ℕ}
    (r : (tensorAction ρ n).IntertwiningMap σ) :
    (action ρ n).IntertwiningMap σ where
  toLinearMap := liftSymmetric (averagedMultilinear r) (averagedMultilinear_symmetric r)
  isIntertwining' g := by
    apply ext_tprod
    intro v
    simp only [LinearMap.comp_apply, action_tprod, liftSymmetric_tprod,
      averagedMultilinear, MultilinearMap.smul_apply, MultilinearMap.sum_apply,
      MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
      map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    simpa only [LinearMap.comp_apply, tensorAction_tprod] using
      LinearMap.congr_fun (r.isIntertwining' g)
        (PiTensorProduct.tprod K (fun j => v (e j)))

theorem quotientAverage_mk {B : Type} [AddCommGroup B] [Module K B]
    {σ : Representation K (Multiplicative E) B}
    {ρ : Representation K (Multiplicative E) A} {n : ℕ}
    (r : (tensorAction ρ n).IntertwiningMap σ) (t : Tensor (K := K) n A) :
    quotientAverage r (SymmetricPower.mk K (Fin n) A t) =
      (n.factorial : K)⁻¹ • ∑ e : Equiv.Perm (Fin n), r (permutation n e t) := by
  classical
  have h : (quotientAverage r).toLinearMap.comp (SymmetricPower.mk K (Fin n) A) =
      (n.factorial : K)⁻¹ • ∑ e : Equiv.Perm (Fin n),
        r.toLinearMap.comp (permutation n e) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change liftSymmetric (averagedMultilinear r) (averagedMultilinear_symmetric r)
      (SymmetricPower.tprod K v) = _
    simp only [
      liftSymmetric_tprod, averagedMultilinear, MultilinearMap.smul_apply,
      MultilinearMap.sum_apply, MultilinearMap.domDomCongr_apply,
      LinearMap.compMultilinearMap_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, permutation_tprod]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    change r (PiTensorProduct.tprod K (fun j => v (e j))) =
      r (permutation n e (PiTensorProduct.tprod K v))
    rw [permutation_tprod]
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    Representation.IntertwiningMap.coe_toLinearMap] using
    LinearMap.congr_fun h t

/-- An actual symmetric multiplication section supplies an actual splitting of
its dual ordered coefficient-sum copy in the genuine symmetric quotient. -/
theorem exists_coefficient_retraction {B : Type} [AddCommGroup B] [Module K B]
    (ρ : Representation K (Multiplicative E) A) (σ : Representation K (Multiplicative E) B)
    (n : ℕ) {I : Type} [Fintype I] (b : Basis I K A)
    (μ : (tensorAction ρ n).IntertwiningMap σ)
    (s : σ.IntertwiningMap (tensorAction ρ n)) (hμs : μ.comp s = .id σ)
    (hperm : ∀ e : Equiv.Perm (Fin n), μ.toLinearMap.comp (permutation n e) = μ.toLinearMap)
    (hfac : (n.factorial : K) ≠ 0) :
    ∃ r : (action ρ.dual n).IntertwiningMap σ.dual,
      r.comp (coefficientInclusion ρ σ n b μ) = .id σ.dual := by
  classical
  let e := dualTensorEquiv ρ n b
  let d := e.symm.toIntertwiningMap.comp (dualIntertwiner μ)
  let r₀ := (dualIntertwiner s).comp e.toIntertwiningMap
  have hr₀ (φ : Dual K B) : r₀ (d φ) = φ := by
    apply LinearMap.ext
    intro x
    change e.toLinearEquiv (e.toLinearEquiv.symm (φ.comp μ.toLinearMap)) (s x) = φ x
    rw [e.toLinearEquiv.apply_symm_apply]
    exact congrArg φ (congrArg (fun q => q x) hμs)
  have hd (f : Equiv.Perm (Fin n)) (φ : Dual K B) : permutation n f (d φ) = d φ := by
    apply e.toLinearEquiv.injective
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change PiTensorProduct.dualDistrib (permutation n f (d φ))
        (PiTensorProduct.tprod K v) =
      PiTensorProduct.dualDistrib (d φ) (PiTensorProduct.tprod K v)
    rw [pair_permutation]
    change e.toLinearEquiv (e.toLinearEquiv.symm (φ.comp μ.toLinearMap))
        (PiTensorProduct.tprod K (fun j => v (f.symm j))) =
      e.toLinearEquiv (e.toLinearEquiv.symm (φ.comp μ.toLinearMap))
        (PiTensorProduct.tprod K v)
    simp only [e.toLinearEquiv.apply_symm_apply]
    simpa only [LinearMap.comp_apply, permutation_tprod] using
      congrArg φ (LinearMap.congr_fun (hperm f.symm) (PiTensorProduct.tprod K v))
  refine ⟨quotientAverage r₀, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro φ
  change quotientAverage r₀ (SymmetricPower.mk K (Fin n) (Dual K A) (d φ)) = φ
  rw [quotientAverage_mk]
  simp_rw [hd, hr₀]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hfac, one_smul]

/-- Raw quotient dualization gives ordered coefficient sums exactly. Repeated
tuples remain repeated terms; no monomial-normalization premise is assumed. -/
theorem coefficientInclusion_basis {B : Type} [AddCommGroup B] [Module K B]
    (ρ : Representation K (Multiplicative E) A) (σ : Representation K (Multiplicative E) B)
    (n : ℕ) {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (b : Basis I K A) (c : Basis J K B)
    (μ : (tensorAction ρ n).IntertwiningMap σ) (degree : (Fin n → I) → J)
    (hμ : ∀ t : Fin n → I, μ (PiTensorProduct.tprod K (fun j => b (t j))) = c (degree t))
    (i : J) :
    coefficientInclusion ρ σ n b μ (c.dualBasis i) =
      ∑ t : Fin n → I, if degree t = i then
        SymmetricPower.tprod K (fun j => b.dualBasis (t j)) else 0 := by
  classical
  change SymmetricPower.mk K (Fin n) (Dual K A)
      (PiTensorProduct.dualDistribInvOfBasis (fun _ : Fin n => b)
        ((c.dualBasis i).comp μ.toLinearMap)) = _
  rw [PiTensorProduct.dualDistribInvOfBasis_apply, map_sum]
  simp only [map_smul, LinearMap.comp_apply, Representation.IntertwiningMap.coe_toLinearMap,
    hμ, Basis.dualBasis_apply_self]
  refine Finset.sum_congr ?_ ?_
  · ext t
    simp only [Finset.mem_univ]
  · intro t _
    split_ifs with h h <;>
      simp_all only [one_smul, zero_smul, map_zero, SymmetricPower.tprod,
        LinearMap.compMultilinearMap_apply, Basis.coe_dualBasis]

end TensorActions

end D5.S3.FiniteGroups.GroupAlgebra.SymmetricPowerBlockSplitting
