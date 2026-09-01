/- GID: D5/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization
   generality: G
   mirror-B: D5/B/S3/Observer/Approximation/ReadoutUpdateCommutatorFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The readout-update commutator factors exactly and has the defect sup norm. -/

import D5.S3.Quantum.ObserverCommutator
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization

open D5.S3.Quantum.ObserverAlgebra
open D5.S3.Quantum.ObserverCommutator
open scoped ENNReal lp

noncomputable section

/-- The source's register Hilbert space `ell^2(I)`. -/
abbrev ObserverHilbertSpace (I : Type*) := lp (fun _ : I => Complex) 2

/-- The update difference `delta_tau f = f o tau^{-1} - f`. -/
def readoutUpdateDefect {I : Type*} (tau : Equiv.Perm I) (f : I -> Complex) : I -> Complex :=
  fun i => f (tau.symm i) - f i

private theorem update_memℓp {I : Type*} (tau : Equiv.Perm I)
    (psi : ObserverHilbertSpace I) :
    Memℓp (fun i => psi (tau.symm i)) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  change Summable ((fun i => ‖psi i‖ ^ (2 : ENNReal).toReal) ∘ tau.symm)
  exact tau.symm.summable_iff.mpr ((memℓp_gen_iff (by norm_num)).mp psi.2)

private def updateVector {I : Type*} (tau : Equiv.Perm I)
    (psi : ObserverHilbertSpace I) : ObserverHilbertSpace I :=
  ⟨fun i => psi (tau.symm i), update_memℓp tau psi⟩

private theorem updateVector_norm {I : Type*} (tau : Equiv.Perm I)
    (psi : ObserverHilbertSpace I) : ‖updateVector tau psi‖ = ‖psi‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sq_eq_re_inner (𝕜 := Complex) (updateVector tau psi),
    norm_sq_eq_re_inner (𝕜 := Complex) psi]
  congr 1
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simpa only [updateVector, Subtype.coe_mk, Function.comp_apply] using
    (tau.symm.tsum_eq (fun i => inner (𝕜 := Complex) (psi i) (psi i)))

/-- Reversible address update as a surjective linear isometry of `ell^2(I)`. -/
noncomputable def updateLinearIsometryEquiv {I : Type*} (tau : Equiv.Perm I) :
    ObserverHilbertSpace I ≃ₗᵢ[Complex] ObserverHilbertSpace I where
  toFun := updateVector tau
  invFun := updateVector tau.symm
  left_inv psi := by
    apply lp.ext
    funext i
    simp [updateVector]
  right_inv psi := by
    apply lp.ext
    funext i
    simp [updateVector]
  map_add' psi phi := by
    apply lp.ext
    funext i
    rfl
  map_smul' c psi := by
    apply lp.ext
    funext i
    rfl
  norm_map' := updateVector_norm tau

@[simp]
theorem updateLinearIsometryEquiv_apply {I : Type*} (tau : Equiv.Perm I)
    (psi : ObserverHilbertSpace I) (i : I) :
    updateLinearIsometryEquiv tau psi i = psi (tau.symm i) := rfl

/-- Natural domain of the possibly unbounded multiplication operator `M_f`. -/
def multiplicationDomain {I : Type*} (f : I -> Complex) :
    Submodule Complex (ObserverHilbertSpace I) where
  carrier := {psi | Memℓp (fun i => f i * psi i) 2}
  zero_mem' := by
    change Memℓp (fun i => f i * (0 : ObserverHilbertSpace I) i) 2
    convert (zero_memℓp : Memℓp (fun _ : I => (0 : Complex)) 2) using 1
    funext i
    simp
  add_mem' := by
    intro psi phi hpsi hphi
    change Memℓp (fun i => f i * (psi + phi : ObserverHilbertSpace I) i) 2
    convert hpsi.add hphi using 1
    funext i
    simp [mul_add]
  smul_mem' := by
    intro c psi hpsi
    change Memℓp (fun i => f i * (c • psi : ObserverHilbertSpace I) i) 2
    convert hpsi.const_smul c using 1
    funext i
    simp only [lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The domain on which both products in `[U_tau, M_f]` are defined. -/
def commutatorDomain {I : Type*} (tau : Equiv.Perm I) (f : I -> Complex) :
    Submodule Complex (ObserverHilbertSpace I) :=
  multiplicationDomain f ⊓
    (multiplicationDomain f).comap (updateLinearIsometryEquiv tau).toLinearEquiv.toLinearMap

private def multipliedVector {I : Type*} (f : I -> Complex)
    (psi : multiplicationDomain f) : ObserverHilbertSpace I :=
  ⟨fun i => f i * psi.1 i, psi.2⟩

/-- The independently constructed commutator `U_tau M_f - M_f U_tau`. -/
noncomputable def readoutUpdateCommutator {I : Type*} (tau : Equiv.Perm I)
    (f : I -> Complex) :
    commutatorDomain tau f →ₗ[Complex] ObserverHilbertSpace I where
  toFun psi :=
    updateLinearIsometryEquiv tau
        (multipliedVector f ⟨psi.1, psi.2.1⟩) -
      multipliedVector f
        ⟨updateLinearIsometryEquiv tau psi.1, psi.2.2⟩
  map_add' psi phi := by
    apply lp.ext
    funext i
    simp only [multipliedVector, updateLinearIsometryEquiv_apply, Submodule.coe_add,
      lp.coeFn_sub, Pi.sub_apply, lp.coeFn_add, Pi.add_apply, Subtype.coe_mk]
    ring
  map_smul' c psi := by
    apply lp.ext
    funext i
    simp only [multipliedVector, updateLinearIsometryEquiv_apply, Submodule.coe_smul,
      lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, Subtype.coe_mk,
      smul_eq_mul, RingHom.id_apply]
    ring

private theorem factored_memℓp {I : Type*} (tau : Equiv.Perm I) (f : I -> Complex)
    (psi : commutatorDomain tau f) :
    Memℓp (fun i => readoutUpdateDefect tau f i * psi.1 (tau.symm i)) 2 := by
  have hleft :
      Memℓp (fun i => f (tau.symm i) * psi.1 (tau.symm i)) 2 :=
    update_memℓp tau (multipliedVector f ⟨psi.1, psi.2.1⟩)
  have hright : Memℓp (fun i => f i * psi.1 (tau.symm i)) 2 := psi.2.2
  convert hleft.sub hright using 1
  funext i
  simp only [Pi.sub_apply, readoutUpdateDefect, sub_mul]

/-- The independently constructed factor `M_(delta_tau f) U_tau` on the common domain. -/
noncomputable def factoredReadoutUpdateCommutator {I : Type*} (tau : Equiv.Perm I)
    (f : I -> Complex) :
    commutatorDomain tau f →ₗ[Complex] ObserverHilbertSpace I where
  toFun psi :=
    ⟨fun i => readoutUpdateDefect tau f i * psi.1 (tau.symm i), factored_memℓp tau f psi⟩
  map_add' psi phi := by
    apply lp.ext
    funext i
    change
      readoutUpdateDefect tau f i * (psi.1 (tau.symm i) + phi.1 (tau.symm i)) =
        readoutUpdateDefect tau f i * psi.1 (tau.symm i) +
          readoutUpdateDefect tau f i * phi.1 (tau.symm i)
    ring
  map_smul' c psi := by
    apply lp.ext
    funext i
    change
      readoutUpdateDefect tau f i * (c * psi.1 (tau.symm i)) =
        c * (readoutUpdateDefect tau f i * psi.1 (tau.symm i))
    ring

private theorem coefficient_memℓp_infty_of_condition {I : Type*} (f : I -> Complex)
    (h : Finite I ∨ Memℓp f ∞) : Memℓp f ∞ := by
  rcases h with hI | hf
  · letI : Finite I := hI
    exact Memℓp.all f
  · exact hf

/-- The coefficient `f` bundled with the boundedness supplied by the source condition. -/
noncomputable def boundedReadoutCoefficient {I : Type*} (f : I -> Complex)
    (h : Finite I ∨ Memℓp f ∞) : lp (fun _ : I => Complex) ∞ :=
  ⟨f, coefficient_memℓp_infty_of_condition f h⟩

private theorem defect_memℓp_infty {I : Type*} (tau : Equiv.Perm I) (f : I -> Complex)
    (h : Finite I ∨ Memℓp f ∞) : Memℓp (readoutUpdateDefect tau f) ∞ := by
  have hf : Memℓp f ∞ := coefficient_memℓp_infty_of_condition f h
  have hshift : Memℓp (fun i => f (tau.symm i)) ∞ := by
    rw [memℓp_infty_iff]
    obtain ⟨C, hC⟩ := (memℓp_infty_iff.mp hf)
    refine ⟨C, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hC ⟨tau.symm i, rfl⟩
  convert hshift.sub hf using 1
  funext i
  rfl

/-- The update defect bundled in `lp infinity`, whose norm is its supremum norm. -/
noncomputable def boundedReadoutDefect {I : Type*} (tau : Equiv.Perm I)
    (f : I -> Complex) (h : Finite I ∨ Memℓp f ∞) :
    lp (fun _ : I => Complex) ∞ :=
  ⟨readoutUpdateDefect tau f, defect_memℓp_infty tau f h⟩

/-- Coordinate multiplication by a bounded coefficient on `ell^2(I)`. -/
noncomputable def diagonalOperator {I : Type*} (g : lp (fun _ : I => Complex) ∞) :
    ObserverHilbertSpace I →L[Complex] ObserverHilbertSpace I :=
  lp.mapCLM 2
    (fun i => (ContinuousLinearMap.lsmul Complex Complex (g i) : Complex →L[Complex] Complex))
    (norm_nonneg g)
    (fun i => by
      simpa using lp.norm_apply_le_norm (p := (∞ : ENNReal)) (by simp) g i)

@[simp]
theorem diagonalOperator_apply {I : Type*} (g : lp (fun _ : I => Complex) ∞)
    (psi : ObserverHilbertSpace I) (i : I) :
    diagonalOperator g psi i = g i * psi i := by
  simp [diagonalOperator, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

@[simp]
theorem boundedReadoutCoefficient_apply {I : Type*} (f : I -> Complex)
    (h : Finite I ∨ Memℓp f ∞) (i : I) : boundedReadoutCoefficient f h i = f i := rfl

@[simp]
theorem boundedReadoutDefect_apply {I : Type*} (tau : Equiv.Perm I) (f : I -> Complex)
    (h : Finite I ∨ Memℓp f ∞) (i : I) :
    boundedReadoutDefect tau f h i = readoutUpdateDefect tau f i := rfl

/-- The multiplication-operator norm is exactly the coefficient supremum norm. -/
theorem diagonalOperator_norm {I : Type*} (g : lp (fun _ : I => Complex) ∞) :
    ‖diagonalOperator g‖ = ‖g‖ := by
  classical
  apply le_antisymm
  · exact lp.norm_mapCLM_le 2
      (fun i => (ContinuousLinearMap.lsmul Complex Complex (g i) : Complex →L[Complex] Complex))
      (norm_nonneg g)
      (fun i => by
        simpa using lp.norm_apply_le_norm (p := (∞ : ENNReal)) (by simp) g i)
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro i
    have happly :
        diagonalOperator g (lp.single (E := fun _ : I => Complex) 2 i (1 : Complex)) =
          lp.single (E := fun _ : I => Complex) 2 i (g i) := by
      apply lp.ext
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [lp.single_apply, Pi.single_apply, hji]
    calc
      ‖g i‖ = ‖lp.single (E := fun _ : I => Complex) 2 i (g i)‖ :=
        (lp.norm_single (E := fun _ : I => Complex) (by norm_num) i (g i)).symm
      _ = ‖diagonalOperator g
          (lp.single (E := fun _ : I => Complex) 2 i (1 : Complex))‖ := by rw [happly]
      _ ≤ ‖diagonalOperator g‖ *
          ‖lp.single (E := fun _ : I => Complex) 2 i (1 : Complex)‖ :=
        (diagonalOperator g).le_opNorm
          (lp.single (E := fun _ : I => Complex) 2 i (1 : Complex))
      _ = ‖diagonalOperator g‖ := by
        have hone : ‖lp.single (E := fun _ : I => Complex) 2 i (1 : Complex)‖ = 1 := by
          simpa using lp.norm_single (E := fun _ : I => Complex) (by norm_num) i (1 : Complex)
        rw [hone, mul_one]

/-- The bounded commutator appearing in the operator-norm assertion. -/
noncomputable def boundedReadoutUpdateCommutator {I : Type*} (tau : Equiv.Perm I)
    (f : I -> Complex) (h : Finite I ∨ Memℓp f ∞) :
    ObserverHilbertSpace I →L[Complex] ObserverHilbertSpace I :=
  (updateLinearIsometryEquiv tau : ObserverHilbertSpace I →L[Complex]
      ObserverHilbertSpace I).comp (diagonalOperator (boundedReadoutCoefficient f h)) -
    (diagonalOperator (boundedReadoutCoefficient f h)).comp
      (updateLinearIsometryEquiv tau : ObserverHilbertSpace I →L[Complex]
        ObserverHilbertSpace I)

private theorem bounded_commutator_factorization {I : Type*} (tau : Equiv.Perm I)
    (f : I -> Complex) (h : Finite I ∨ Memℓp f ∞) :
    boundedReadoutUpdateCommutator tau f h =
      (diagonalOperator (boundedReadoutDefect tau f h)).comp
        (updateLinearIsometryEquiv tau : ObserverHilbertSpace I →L[Complex]
          ObserverHilbertSpace I) := by
  ext psi i
  simp only [boundedReadoutUpdateCommutator, sub_apply,
    ContinuousLinearMap.comp_apply, diagonalOperator_apply,
    updateLinearIsometryEquiv_apply, boundedReadoutCoefficient_apply,
    boundedReadoutDefect_apply]
  exact
    congrFun (observer_read_update_commutator_formula tau f psi) i

/-- The readout-update commutator factors on its natural common domain, and under
the source's finite-or-bounded condition its operator norm is exactly the
supremum norm of the update defect. -/
theorem readout_update_commutator_factorization {I : Type*}
    (tau : Equiv.Perm I) (f : I -> Complex) :
    readoutUpdateCommutator tau f = factoredReadoutUpdateCommutator tau f ∧
      ∀ h : Finite I ∨ Memℓp f ∞,
        ‖boundedReadoutUpdateCommutator tau f h‖ = ‖boundedReadoutDefect tau f h‖ := by
  constructor
  · apply LinearMap.ext
    intro psi
    apply lp.ext
    funext i
    change
      f (tau.symm i) * psi.1 (tau.symm i) - f i * psi.1 (tau.symm i) =
        readoutUpdateDefect tau f i * psi.1 (tau.symm i)
    simpa only [readoutUpdateDefect, observerUpdate, readObservable, Pi.sub_apply] using
      congrFun (observer_read_update_commutator_formula tau f psi.1) i
  · intro h
    rw [bounded_commutator_factorization]
    rw [ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
    exact diagonalOperator_norm (boundedReadoutDefect tau f h)
#print axioms readout_update_commutator_factorization

private noncomputable def boolSwap : Equiv.Perm Bool := Equiv.swap false true

private def boolReadout : Bool -> Complex := fun b => if b then 1 else 0

example : readoutUpdateDefect boolSwap boolReadout true ≠ 0 := by
  norm_num [readoutUpdateDefect, boolSwap, boolReadout, Equiv.swap_apply_def]

example {I : Type*} (tau : Equiv.Perm I) (f : I -> Complex)
    (psi : commutatorDomain tau f) (i : I) :
    readoutUpdateCommutator tau f psi i =
      readoutUpdateDefect tau f i * psi.1 (tau.symm i) := by
  have h := congrArg (fun op => op psi)
    (readout_update_commutator_factorization tau f).1
  exact congrArg (fun vector => vector i) h

example :
    ‖boundedReadoutUpdateCommutator boolSwap boolReadout (Or.inl inferInstance)‖ =
      ‖boundedReadoutDefect boolSwap boolReadout (Or.inl inferInstance)‖ :=
  (readout_update_commutator_factorization boolSwap boolReadout).2 (Or.inl inferInstance)

end

end D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
