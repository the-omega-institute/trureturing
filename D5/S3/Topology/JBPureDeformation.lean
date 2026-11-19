/- GID: D5/S3/Topology/JBPureDeformation
   generality: G
   mirror-B: D5/B/S3/Topology/JBPureDeformation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Extreme]
   utility: none
   digest: Normalized quadratic pullbacks deform pure states on the same complete JB carrier. -/

module

public import D5.S3.Topology.JBComplexification
public import Mathlib.Analysis.Convex.Extreme

/-! Pure-state transport by the quadratic maps of the original JB carrier. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped Topology

namespace D5.S3.Topology.JBPureDeformation
open JBAlgebra JBPositiveShift JBComplexification
open Filter

private theorem projective_extreme {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : Set V) (m : V →ₗ[ℝ] ℝ)
    (hsmul : ∀ r : ℝ, 0 ≤ r → ∀ x ∈ C, r • x ∈ C)
    (hmass : ∀ x ∈ C, x ≠ 0 → 0 < m x)
    (T : V ≃ₗ[ℝ] V) (hT : ∀ x, T x ∈ C ↔ x ∈ C)
    (x : V) (hx : x ∈ ({z | z ∈ C ∧ m z = 1} : Set V).extremePoints ℝ) :
    (m (T x))⁻¹ • T x ∈
      ({z | z ∈ C ∧ m z = 1} : Set V).extremePoints ℝ := by
  let B : Set V := {z | z ∈ C ∧ m z = 1}
  have xne : x ≠ 0 := by intro h; simpa [h] using hx.1.2
  have mp : 0 < m (T x) := hmass _ ((hT x).mpr hx.1.1) (by
    intro h; exact xne (T.injective (by simpa using h)))
  refine ⟨⟨hsmul _ (inv_nonneg.mpr mp.le) _ ((hT x).mpr hx.1.1), ?_⟩, ?_⟩
  · simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ mp.ne']
  · intro y hy z hz hseg
    rcases hseg with ⟨a, b, ha, hb, hab, heq⟩
    have yp : T.symm y ∈ C := (hT _).mp (by simpa using hy.1)
    have zp : T.symm z ∈ C := (hT _).mp (by simpa using hz.1)
    have my : 0 < m (T.symm y) := hmass _ yp (by
      intro h; have : y = 0 := by simpa using congrArg T h
      simpa [this] using hy.2)
    have mz : 0 < m (T.symm z) := hmass _ zp (by
      intro h; have : z = 0 := by simpa using congrArg T h
      simpa [this] using hz.2)
    let y' := (m (T.symm y))⁻¹ • T.symm y
    let z' := (m (T.symm z))⁻¹ • T.symm z
    have hy' : y' ∈ B := ⟨hsmul _ (inv_nonneg.mpr my.le) _ yp, by
      simp [y', my.ne']⟩
    have hz' : z' ∈ B := ⟨hsmul _ (inv_nonneg.mpr mz.le) _ zp, by
      simp [z', mz.ne']⟩
    have hinv : a • T.symm y + b • T.symm z = (m (T x))⁻¹ • x := by
      simpa only [map_add, map_smul, T.symm_apply_apply] using congrArg T.symm heq
    have hmassEq := congrArg m hinv
    simp only [map_add, map_smul, smul_eq_mul, hx.1.2, mul_one] at hmassEq
    have hweights : m (T x) * a * m (T.symm y) +
        m (T x) * b * m (T.symm z) = 1 := by
      calc
        _ = m (T x) * (a * m (T.symm y) + b * m (T.symm z)) := by ring
        _ = 1 := by rw [hmassEq, mul_inv_cancel₀ mp.ne']
    have hcomb : (m (T x) * a * m (T.symm y)) • y' +
        (m (T x) * b * m (T.symm z)) • z' = x := by
      dsimp only [y', z']
      simp only [smul_smul, mul_assoc, mul_inv_cancel₀ my.ne',
        mul_inv_cancel₀ mz.ne', mul_one]
      rw [mul_smul, mul_smul, ← smul_add, hinv, smul_smul,
        mul_inv_cancel₀ mp.ne', one_smul]
    have hyx : y' = x := hx.2 hy' hz'
      ⟨_, _, mul_pos (mul_pos mp ha) my, mul_pos (mul_pos mp hb) mz,
        hweights, hcomb⟩
    have hTy : (m (T.symm y))⁻¹ • y = T x := by
      simpa only [y', map_smul, T.apply_symm_apply] using congrArg T hyx
    have hmy : (m (T.symm y))⁻¹ = m (T x) := by
      simpa only [map_smul, smul_eq_mul, hy.2, mul_one] using congrArg m hTy
    rw [hmy] at hTy
    calc
      y = (m (T x))⁻¹ • (m (T x) • y) := by
        rw [smul_smul, inv_mul_cancel₀ mp.ne', one_smul]
      _ = (m (T x))⁻¹ • T x := by rw [hTy]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {S : X →ₗ[ℝ] X →ₗ[ℝ] X} {u : X}

/-- The normalized positive continuous functionals for the original square cone. -/
def states (S : X →ₗ[ℝ] X →ₗ[ℝ] X) (u : X) : Set (X →L[ℝ] ℝ) :=
  {β | (∀ x : X, 0 ≤ β (S x x)) ∧ β u = 1}

/-- The continuous quadratic representation on the specified original carrier. -/
def quadOp (A : Data X S u) (a : X) : X →L[ℝ] X :=
  (2 : ℝ) • ((lmul A a).comp (lmul A a)) - lmul A (S a a)

private theorem positive_mass (A : Data X S u) (β : X →L[ℝ] ℝ)
    (hp : ∀ x, 0 ≤ β (S x x)) (hne : β ≠ 0) : 0 < β u := by
  have h0 : 0 ≤ β u := by simpa only [A.unit_mul] using hp u
  apply lt_of_le_of_ne h0
  intro hz
  have hz' : β u = 0 := hz.symm
  apply hne
  ext x
  change β x = 0
  obtain ⟨a, ha⟩ := square_of_ambient_center A (‖x‖ • u + x) ‖x‖ (norm_nonneg x)
    (by simpa only [add_sub_cancel_left] using (le_rfl : ‖x‖ ≤ ‖x‖))
  obtain ⟨b, hb⟩ := square_of_ambient_center A (‖x‖ • u - x) ‖x‖ (norm_nonneg x)
    (by simpa only [sub_sub_cancel_left, norm_neg] using (le_rfl : ‖x‖ ≤ ‖x‖))
  have hpa := hp a
  have hpb := hp b
  rw [ha, map_add, map_smul, hz', smul_zero, zero_add] at hpa
  rw [hb, map_sub, map_smul, hz', smul_zero, zero_sub] at hpb
  exact le_antisymm (by linarith) hpa

private theorem quadratic_inverse_positive (A : Data X S u) (a : X)
    (hQ : Function.Bijective (quadratic S a))
    (e : X ≃L[ℝ] X) (he : ∀ v, e v = quadratic S a v) (x : X) :
    ∃ y : X, e.symm (S x x) = S y y := by
  obtain ⟨b, hb⟩ := hQ.2 u
  have hinv (v : X) : quadratic S a (quadratic S b (quadratic S a v)) = v := by
    rw [← fundamental_identity A, hb]
    simp only [quadratic, A.unit_mul, two_smul, add_sub_cancel_right]
  obtain ⟨y, hy⟩ := quadratic_preserves_squares A a x
  obtain ⟨z, hz⟩ := quadratic_preserves_squares A b y
  refine ⟨z, ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, he, ← hz, ← hy, hinv]

private theorem quadratic_pure (A : Data X S u) (a : X)
    (hQ : Function.Bijective (quadratic S a))
    (β : X →L[ℝ] ℝ) (hβ : β ∈ (states S u).extremePoints ℝ) :
    ((β (quadratic S a u))⁻¹ • β.comp (quadOp A a)) ∈
      (states S u).extremePoints ℝ := by
  let e : X ≃L[ℝ] X := ContinuousLinearEquiv.ofBijective (quadOp A a)
    (LinearMap.ker_eq_bot.mpr hQ.1) (LinearMap.range_eq_top.mpr hQ.2)
  have he (v : X) : e v = quadratic S a v := rfl
  let T : (X →L[ℝ] ℝ) ≃ₗ[ℝ] (X →L[ℝ] ℝ) :=
    { toFun := fun f => f.comp e.toContinuousLinearMap
      invFun := fun f => f.comp e.symm.toContinuousLinearMap
      left_inv := by intro f; ext v; simp
      right_inv := by intro f; ext v; simp
      map_add' := by intro f g; rfl
      map_smul' := by intro r f; rfl }
  let C : Set (X →L[ℝ] ℝ) := {f | ∀ x, 0 ≤ f (S x x)}
  let m : (X →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => f u
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hT (f : X →L[ℝ] ℝ) : T f ∈ C ↔ f ∈ C := by
    constructor
    · intro hf x
      obtain ⟨y, hy⟩ := quadratic_inverse_positive A a hQ e he x
      have h := hf y
      change 0 ≤ f (e (S y y)) at h
      rwa [← hy, e.apply_symm_apply] at h
    · intro hf x
      obtain ⟨y, hy⟩ := quadratic_preserves_squares A a x
      change 0 ≤ f (e (S x x))
      rw [he, hy]
      exact hf y
  exact projective_extreme C m (by
    intro r hr f hf x
    exact mul_nonneg hr (hf x)) (fun f hf hn => positive_mass A f hf hn) T hT β hβ

/-- The actual polynomial quadratic representation near the specified unit. -/
def perturbation (A : Data X S u) (h : X) (t : ℝ) : X →L[ℝ] X :=
  1 + (2 * t) • lmul A h + t ^ 2 • quadOp A h

omit [CompleteSpace X] in
private theorem perturbation_apply (A : Data X S u) (h : X) (t : ℝ) (v : X) :
    perturbation A h t v = quadratic S (u + t • h) v := by
  have hr (x : X) : S x u = x := (A.symm x u).trans (A.unit_mul x)
  simp only [perturbation, quadOp, lmul, quadratic, add_apply,
    smul_apply, one_apply_eq_self,
    sub_apply, ContinuousLinearMap.comp_apply,
    LinearMap.mkContinuous_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, A.unit_mul, hr]
  module

/-- Normalization uses the transformed mass, on the same original JB carrier. -/
def deformation (A : Data X S u) (β : X →L[ℝ] ℝ) (h : X) (t : ℝ) : X →L[ℝ] ℝ :=
  (β (perturbation A h t u))⁻¹ • β.comp (perturbation A h t)

/-- Pure states with zero first moment and positive second moment admit actual
pure quadratic deformations detecting the same element, converging in dual norm.
All square roots, quadratic maps and state functionals stay on the same JB carrier. -/
theorem pure_deformation (A : Data X S u) (β : X →L[ℝ] ℝ)
    (hβ : β ∈ (states S u).extremePoints ℝ) (h : X)
    (hz : β h = 0) (hq : 0 < β (S h h)) :
    (∀ᶠ t : ℝ in 𝓝[≠] 0,
      (∃ a : X, S a a = u + t • h) ∧
      Function.Bijective (quadratic S (u + t • h)) ∧
      0 < β (quadratic S (u + t • h) u) ∧
      deformation A β h t ∈ (states S u).extremePoints ℝ ∧
      deformation A β h t h =
        (2 * t * β (S h h) + t ^ 2 * β (S h (S h h))) /
          (1 + t ^ 2 * β (S h h)) ∧
      deformation A β h t h ≠ 0) ∧
    Tendsto (deformation A β h) (𝓝 0) (𝓝 β) := by
  have hr (x : X) : S x u = x := (A.symm x u).trans (A.unit_mul x)
  have hunit (t : ℝ) : β (perturbation A h t u) = 1 + t ^ 2 * β (S h h) := by
    simp only [perturbation, quadOp, add_apply,
      smul_apply, one_apply_eq_self,
      sub_apply, ContinuousLinearMap.comp_apply,
      lmul, LinearMap.mkContinuous_apply, hr,
      map_add, map_smul, map_sub, smul_eq_mul, hβ.1.2, hz]
    ring
  have hmass (t : ℝ) : 0 < β (perturbation A h t u) := by
    rw [hunit]
    positivity
  have hformula (t : ℝ) : deformation A β h t h =
      (2 * t * β (S h h) + t ^ 2 * β (S h (S h h))) /
        (1 + t ^ 2 * β (S h h)) := by
    have hn : β (perturbation A h t h) =
        2 * t * β (S h h) + t ^ 2 * β (S h (S h h)) := by
      simp only [perturbation, quadOp, add_apply,
        smul_apply, one_apply_eq_self,
        sub_apply, ContinuousLinearMap.comp_apply,
        lmul, LinearMap.mkContinuous_apply, A.symm (S h h) h,
        map_add, map_smul, map_sub, smul_eq_mul, hz]
      ring
    simp only [deformation, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, hn, hunit, div_eq_mul_inv]
    ring
  have hc : Continuous (perturbation A h) := by
    unfold perturbation
    fun_prop
  have hp0 : perturbation A h 0 = 1 := by simp [perturbation]
  have hbij : ∀ᶠ t : ℝ in 𝓝 0, Function.Bijective (quadratic S (u + t • h)) := by
    have hi : ∀ᶠ t : ℝ in 𝓝 0, IsUnit (perturbation A h t) :=
      (hc.continuousAt (x := 0)) (by simpa only [hp0] using
        (Units.isOpen.mem_nhds (isUnit_one : IsUnit (1 : X →L[ℝ] X))))
    filter_upwards [hi] with t ht
    have hbi := ContinuousLinearMap.isUnit_iff_bijective.mp ht
    have hf : (perturbation A h t : X → X) = quadratic S (u + t • h) :=
      funext (perturbation_apply A h t)
    rw [← hf]
    exact hbi
  have hsquare : ∀ᶠ t : ℝ in 𝓝 0, ∃ a : X, S a a = u + t • h := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖t • h‖ < 1 := by
      have hcont : Continuous (fun t : ℝ => ‖t • h‖) := by fun_prop
      exact hcont.continuousAt.eventually (gt_mem_nhds (by simp))
    filter_upwards [hsmall] with t ht
    exact square_of_ambient_center A (u + t • h) 1 zero_le_one
      (by simpa only [one_smul, add_sub_cancel_left] using ht.le)
  have hfactor : ∀ᶠ t : ℝ in 𝓝 0,
      0 < 2 * β (S h h) + t * β (S h (S h h)) := by
    have hcont : Continuous (fun t : ℝ =>
        2 * β (S h h) + t * β (S h (S h h))) := by fun_prop
    exact (hcont.continuousAt (x := 0)).eventually
      (lt_mem_nhds (by simpa only [zero_mul, add_zero] using
        (show 0 < 2 * β (S h h) by positivity)))
  constructor
  · filter_upwards [hbij.filter_mono nhdsWithin_le_nhds,
      hsquare.filter_mono nhdsWithin_le_nhds,
      hfactor.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hs hf htn
    have htne : t ≠ 0 := htn
    have hqu : (quadOp A (u + t • h)) = perturbation A h t := by
      ext v
      exact (perturbation_apply A h t v).symm
    have hpure := quadratic_pure A (u + t • h) ht β hβ
    refine ⟨hs, ht, ?_, ?_, hformula t, ?_⟩
    · simpa only [← perturbation_apply A h t u] using hmass t
    · simpa only [← perturbation_apply A h t u, hqu, deformation] using hpure
    · rw [hformula]
      apply div_ne_zero
      · have hn : 2 * t * β (S h h) + t ^ 2 * β (S h (S h h)) =
            t * (2 * β (S h h) + t * β (S h (S h h))) := by ring
        rw [hn]
        exact mul_ne_zero htne hf.ne'
      · positivity
  · have hcont : ContinuousAt (deformation A β h) 0 := by
      unfold deformation
      have hm : ContinuousAt (fun t : ℝ => β (perturbation A h t u)) 0 :=
        β.continuous.continuousAt.comp
          ((hc.continuousAt (x := 0)).clm_apply continuousAt_const)
      have hi := hm.inv₀ (by simpa only [hp0, one_apply_eq_self, hβ.1.2] using
        (one_ne_zero : (1 : ℝ) ≠ 0))
      have ho : ContinuousAt (fun t : ℝ => β.comp (perturbation A h t)) 0 :=
        (ContinuousLinearMap.compL ℝ X X ℝ β).continuous.continuousAt.comp
          hc.continuousAt
      exact hi.smul ho
    have hd0 : deformation A β h 0 = β := by
      ext x
      simp [deformation, hp0, hβ.1.2, one_apply_eq_self]
    simpa only [hd0] using hcont.tendsto

#print axioms pure_deformation

end D5.S3.Topology.JBPureDeformation
