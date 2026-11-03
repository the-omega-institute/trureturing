/- GID: D5/S3/Quantum/Algebra/PauliLocalBounds
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PauliLocalBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Exact Euclidean bounds and the action Gram operator of the Pauli perturbation. -/

import D5.S3.Quantum.Algebra.PauliFixedProductFamily
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open WithLp
open scoped InnerProductSpace
namespace D5.S3.Quantum.Algebra.PauliFixedProductFamily

private theorem sqrt_two_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
private theorem sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-- The common attaining direction for the spin product and diagonal defect. -/
def balanced : J := (Real.sqrt 2)⁻¹ • (e 0 + e 1)

private theorem balanced_norm : ‖balanced‖ = 1 := by
  have hn : ‖balanced‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [balanced, e, PiLp.single_apply, Fin.sum_univ_succ]
    field_simp
    nlinarith [sqrt_two_sq]
  nlinarith [norm_nonneg balanced]

private theorem spin_bound (a b : J) : ‖S a b‖ ≤ Real.sqrt 2 * ‖a‖ * ‖b‖ := by
  have hid : ‖S a b‖^2 +
      (a 0*b 0-a 1*b 1-a 2*b 2-a 3*b 3)^2 +
      (a 0*b 1-b 0*a 1)^2 + (a 0*b 2-b 0*a 2)^2 + (a 0*b 3-b 0*a 3)^2 +
      2*((a 1*b 2-a 2*b 1)^2+(a 2*b 3-a 3*b 2)^2+(a 3*b 1-a 1*b 3)^2) =
      2 * ‖a‖^2 * ‖b‖^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, S, spin, Fin.sum_univ_succ]
    <;> ring
  have h : ‖S a b‖^2 ≤ 2*‖a‖^2*‖b‖^2 := by
    nlinarith [sq_nonneg (a 0*b 0-a 1*b 1-a 2*b 2-a 3*b 3),
      sq_nonneg (a 0*b 1-b 0*a 1), sq_nonneg (a 0*b 2-b 0*a 2),
      sq_nonneg (a 0*b 3-b 0*a 3), sq_nonneg (a 1*b 2-a 2*b 1),
      sq_nonneg (a 2*b 3-a 3*b 2), sq_nonneg (a 3*b 1-a 1*b 3)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa [mul_pow, sqrt_two_sq] using h

private theorem d_bound (t : ℝ) (a b : J) :
    ‖D t a b‖ ≤ Real.sqrt (1+t^2) * ‖a‖ * ‖b‖ := by
  let q := a 1^2+a 2^2+(a 3+t*a 0)^2
  have hid : ‖D t a b‖^2 +
      ((a 0-t*a 3)^2+t^2*(a 1^2+a 2^2))*‖b‖^2 +
      q*b 0^2 + (a 1*b 1+a 2*b 2+(a 3+t*a 0)*b 3)^2 =
      (1+t^2)*‖a‖^2*‖b‖^2 := by
    simp [q, EuclideanSpace.real_norm_sq_eq, D, C, cross, cross_apply, shift,
      Fin.sum_univ_succ]
    <;> ring
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hp : 0 ≤ ((a 0-t*a 3)^2+t^2*(a 1^2+a 2^2))*‖b‖^2 := by positivity
  have h : ‖D t a b‖^2 ≤ (1+t^2)*‖a‖^2*‖b‖^2 := by
    nlinarith [mul_nonneg hq (sq_nonneg (b 0)),
      sq_nonneg (a 1*b 1+a 2*b 2+(a 3+t*a 0)*b 3)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa [mul_pow, Real.sq_sqrt (show 0 ≤ 1+t^2 by positivity)] using h

private theorem self_bound (t : ℝ) (a : J) : ‖D t a a‖ ≤ |t|/2*‖a‖^2 := by
  have hid : 4*‖D t a a‖^2 +
      t^2*(a 0^2-a 1^2-a 2^2-a 3^2)^2+4*t^2*a 0^2*a 3^2 =
      t^2*(‖a‖^2)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, D, C, cross, cross_apply, shift,
      Fin.sum_univ_succ]
    <;> ring
  have h : 4*‖D t a a‖^2 ≤ t^2*(‖a‖^2)^2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (a 0^2-a 1^2-a 2^2-a 3^2)),
      mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg (a 0))) (sq_nonneg (a 3))]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have ht : |t|^2 = t^2 := sq_abs t
  nlinarith

private theorem unit_bound (t : ℝ) (b : J) : ‖D t (e 0) b‖ ≤ |t|*‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp [EuclideanSpace.real_norm_sq_eq, D, C, cross, cross_apply, shift, e,
    PiLp.single_apply, Fin.sum_univ_succ, mul_pow, sq_abs]
  nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (b 0)),
    mul_nonneg (sq_nonneg t) (sq_nonneg (b 3))]

private theorem self_attained (t : ℝ) : ‖D t balanced balanced‖ = |t|/2 := by
  have hsq : ‖D t balanced balanced‖^2 = t^2/4 := by
    simp [EuclideanSpace.real_norm_sq_eq, balanced, D, C, cross, cross_apply,
      shift, e, PiLp.single_apply, Fin.sum_univ_succ]
    field_simp
    nlinarith [sqrt_two_sq]
  have ht : |t|^2 = t^2 := sq_abs t
  nlinarith [norm_nonneg (D t balanced balanced), abs_nonneg t]

private theorem unit_attained (t : ℝ) : ‖D t (e 0) (e 1)‖ = |t| := by
  have heq : D t (e 0) (e 1) = t • e 2 := by
    ext i; fin_cases i <;> simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply]
  rw [heq, norm_smul]
  simp [e]

/-- The actual unit generator as a continuous operator on the fixed Euclidean space. -/
def unitOperator (t : ℝ) : J →L[ℝ] J := (D t (e 0)).toContinuousLinearMap

private theorem unit_opnorm (t : ℝ) : ‖unitOperator t‖=|t| := by
  apply le_antisymm
  · exact (unitOperator t).opNorm_le_bound (abs_nonneg t) (unit_bound t)
  · have hh := (unitOperator t).le_opNorm (e 1)
    change ‖D t (e 0) (e 1)‖≤‖unitOperator t‖*‖e 1‖ at hh
    rw [unit_attained] at hh
    simpa [e] using hh

/-- The original local defect and unit-generator bounds are attained in the same family. -/
theorem exact_defects (t : ℝ) :
    IsGreatest {r : ℝ | ∃ a : J, ‖a‖=1 ∧ r=‖D t a a‖} (|t|/2) ∧
    IsGreatest {r : ℝ | ∃ b : J, ‖b‖=1 ∧ r=‖D t (e 0) b‖} |t| ∧
    (∀ a b : J, ‖S a b‖ ≤ Real.sqrt 2*‖a‖*‖b‖) ∧
    (∀ a b : J, ‖D t a b‖ ≤ Real.sqrt (1+t^2)*‖a‖*‖b‖) ∧
    ‖unitOperator t‖=|t| := by
  refine ⟨⟨⟨balanced, balanced_norm, (self_attained t).symm⟩, ?_⟩,
    ⟨⟨e 1, by simp [e], (unit_attained t).symm⟩, ?_⟩, spin_bound, d_bound t,unit_opnorm t⟩
  · rintro r ⟨a, ha, rfl⟩
    simpa [ha] using self_bound t a
  · rintro r ⟨b, hb, rfl⟩
    simpa [hb] using unit_bound t b


/-- The actual action Gram operator, using adjoints for the fixed Euclidean inner product. -/
def actionGram (t : ℝ) : J →ₗ[ℝ] J :=
  ∑ i : Fin 4, (LinearMap.adjoint (D t (e i))).comp (D t (e i))

private theorem d_adjoint (t : ℝ) (a : J) : LinearMap.adjoint (D t a) = -D t a := by
  ext b
  apply ext_inner_right ℝ
  intro c
  rw [LinearMap.adjoint_inner_left]
  simp [PiLp.inner_apply, D, C, cross, cross_apply, shift, Fin.sum_univ_succ,
    RCLike.inner_apply]
  <;> ring

private theorem gram_coordinates (t : ℝ) (a : J) :
    actionGram t a = toLp 2 ![0,(2+t^2)*a 1,(2+t^2)*a 2,2*a 3] := by
  simp only [actionGram, d_adjoint]
  ext i; fin_cases i <;>
    simp [Fin.sum_univ_succ, D, C, cross, cross_apply, shift, e, PiLp.single_apply] <;> ring

private theorem common_kernel (t : ℝ) (a : J) :
    (∀ i : Fin 4, D t (e i) a = 0) ↔ a 1=0 ∧ a 2=0 ∧ a 3=0 := by
  constructor
  · intro h
    have hx := h 1
    have hy := h 2
    have hx2 := congrArg (fun v : J => v 2) hx
    have hx3 := congrArg (fun v : J => v 3) hx
    have hy3 := congrArg (fun v : J => v 3) hy
    simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply] at hx2 hx3 hy3
    exact ⟨hy3, hx3, by linarith⟩
  · rintro ⟨h1,h2,h3⟩ i
    fin_cases i <;> ext k <;> fin_cases k <;>
      simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply, h1,h2,h3]

private theorem scalar_axis (a : J) :
    (a 1=0 ∧ a 2=0 ∧ a 3=0) ↔ ∃ r : ℝ, a = r • e 0 := by
  constructor
  · rintro ⟨h1,h2,h3⟩
    refine ⟨a 0, ?_⟩
    ext i; fin_cases i <;> simp [e, PiLp.single_apply, h1,h2,h3]
  · rintro ⟨r,rfl⟩
    simp [e, PiLp.single_apply]

private theorem label_kernel (t : ℝ) (a : J) :
    D t a = 0 ↔ ∃ r : ℝ, a = r • (e 0-t • e 3) := by
  constructor
  · intro h
    have hx := LinearMap.congr_fun h (e 1)
    have hy := LinearMap.congr_fun h (e 2)
    have hx2 := congrArg (fun v : J => v 2) hx
    have hx3 := congrArg (fun v : J => v 3) hx
    have hy3 := congrArg (fun v : J => v 3) hy
    simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply] at hx2 hx3 hy3
    refine ⟨a 0, ?_⟩
    ext i; fin_cases i <;> simp [e, PiLp.single_apply]
    · linarith
    · linarith
    · linarith
  · rintro ⟨r,rfl⟩
    ext b i; fin_cases i <;>
      simp [D, C, cross, cross_apply, shift, e, PiLp.single_apply] <;> ring

/-- The span of all actual local table outputs. -/
def actionSupport (t : ℝ) : Submodule ℝ J :=
  Submodule.span ℝ (Set.range (fun p : Fin 4 × Fin 4 => D t (e p.1) (e p.2)))

private theorem support_coordinates (t : ℝ) (a : J) : a ∈ actionSupport t ↔ a 0=0 := by
  constructor
  · intro ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro v ⟨p,rfl⟩
      simp [D,C,cross,cross_apply]
    · rfl
    · intro a b ha hb
      simp_all
    · intro r a ha
      simp_all
  · intro ha
    have hx : e 1 ∈ actionSupport t := by
      have heq : D t (e 2) (e 3) = e 1 := by
        ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
      exact heq ▸ Submodule.subset_span (Set.mem_range_self (2,3))
    have hy : e 2 ∈ actionSupport t := by
      have heq : D t (e 3) (e 1) = e 2 := by
        ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
      exact heq ▸ Submodule.subset_span (Set.mem_range_self (3,1))
    have hz : e 3 ∈ actionSupport t := by
      have heq : D t (e 1) (e 2) = e 3 := by
        ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
      exact heq ▸ Submodule.subset_span (Set.mem_range_self (1,2))
    have heq : a = a 1 • e 1 + a 2 • e 2 + a 3 • e 3 := by
      ext i; fin_cases i <;> simp [e,PiLp.single_apply,ha]
    rw [heq]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hy)) (Submodule.smul_mem _ _ hz)

private theorem gram_eigenvalues (t lam : ℝ) :
    (∃ a : J, a ≠ 0 ∧ actionGram t a = lam • a) ↔
      lam=0 ∨ lam=2+t^2 ∨ lam=2 := by
  constructor
  · rintro ⟨a,ha,heq⟩
    by_cases h0 : lam=0
    · exact Or.inl h0
    by_cases hxy : lam=2+t^2
    · exact Or.inr (Or.inl hxy)
    by_cases hz : lam=2
    · exact Or.inr (Or.inr hz)
    exfalso
    apply ha
    ext i
    have h := congrArg (fun v : J => v i) heq
    fin_cases i
    · simp [gram_coordinates] at h
      exact (mul_eq_zero.mp h.symm).resolve_left h0
    · simp [gram_coordinates] at h
      have hp : (2+t^2-lam)*a 1=0 := by nlinarith
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (Ne.symm hxy))
    · simp [gram_coordinates] at h
      have hp : (2+t^2-lam)*a 2=0 := by nlinarith
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (Ne.symm hxy))
    · simp [gram_coordinates] at h
      have hp : (2-lam)*a 3=0 := by nlinarith
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (Ne.symm hz))
  · rintro (rfl|rfl|rfl)
    · refine ⟨e 0, ?_, ?_⟩
      · simp [e]
      · ext i; fin_cases i <;> simp [gram_coordinates,e,PiLp.single_apply]
    · refine ⟨e 1, ?_, ?_⟩
      · simp [e]
      · ext i; fin_cases i <;> simp [gram_coordinates,e,PiLp.single_apply]
    · refine ⟨e 3, ?_, ?_⟩
      · simp [e]
      · ext i; fin_cases i <;> simp [gram_coordinates,e,PiLp.single_apply]

/-- The same actual action has its exact Gram diagonal, fixed kernel, spatial support and spectrum. -/
theorem exact_action_data (t : ℝ) :
    (∀ a : J, actionGram t a = toLp 2 ![0,(2+t^2)*a 1,(2+t^2)*a 2,2*a 3]) ∧
    (∀ a : J, (∀ i : Fin 4, D t (e i) a=0) ↔ ∃ r : ℝ, a=r • e 0) ∧
    (∀ a : J, a ∈ actionSupport t ↔ a 0=0) ∧
    (∀ a : J, D t a=0 ↔ ∃ r : ℝ, a=r • (e 0-t • e 3)) ∧
    (∀ lam : ℝ, (∃ a : J, a≠0 ∧ actionGram t a=lam • a) ↔
      lam=0 ∨ lam=2+t^2 ∨ lam=2) := by
  refine ⟨gram_coordinates t, ?_, support_coordinates t, label_kernel t, gram_eigenvalues t⟩
  intro a
  exact (common_kernel t a).trans (scalar_axis a)


/-- A unit label attaining the exact bilinear action constant. -/
def extremalLabel (t : ℝ) : J :=
  (Real.sqrt (1+t^2))⁻¹ • (t • e 0+e 3)

private theorem extremal_norm (t : ℝ) : ‖extremalLabel t‖=1 := by
  have hp : 0<Real.sqrt (1+t^2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0≤1+t^2 by positivity)
  have hn : ‖extremalLabel t‖^2=1 := by
    simp [EuclideanSpace.real_norm_sq_eq,extremalLabel,e,PiLp.single_apply,
      Fin.sum_univ_succ]
    field_simp
    nlinarith
  nlinarith [norm_nonneg (extremalLabel t)]

private theorem d_attained (t : ℝ) :
    ‖D t (extremalLabel t) (e 1)‖=Real.sqrt (1+t^2) := by
  have hp : 0<Real.sqrt (1+t^2) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (show 0≤1+t^2 by positivity)
  have heq : D t (extremalLabel t) (e 1)=Real.sqrt (1+t^2) • e 2 := by
    ext i; fin_cases i <;>
      simp [extremalLabel,D,C,cross,cross_apply,shift,e,PiLp.single_apply]
    field_simp
    nlinarith
  rw [heq,norm_smul]
  simp [e,abs_of_pos hp]

private theorem spin_attained : ‖S balanced balanced‖=Real.sqrt 2 := by
  have hs := sqrt_two_sq
  have hn : ‖S balanced balanced‖^2=2 := by
    simp [EuclideanSpace.real_norm_sq_eq,S,spin,balanced,e,PiLp.single_apply,
      Fin.sum_univ_succ]
    field_simp
    nlinarith
  nlinarith [norm_nonneg (S balanced balanced),sqrt_two_pos]

/-- The finite curvature entry uses the original complete basis and spin multiplication. -/
def curvature (i j k : Fin 4) : J := S (e i) (S (e j) (e k))-S (e j) (S (e i) (e k))

private theorem curvature_bound (i j k : Fin 4) : ‖curvature i j k‖≤1 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [curvature,EuclideanSpace.real_norm_sq_eq,S,spin,e,PiLp.single_apply,
      Fin.sum_univ_succ]

private theorem curvature_attained : ‖curvature 1 2 2‖=1 := by
  have h : curvature 1 2 2=e 1 := by
    ext i; fin_cases i <;> norm_num [curvature,S,spin,e,PiLp.single_apply]
  simp [h,e]

/-- Exact local constants, with attaining inputs rather than only upper bounds. -/
theorem exact_constants (t : ℝ) :
    ‖e 0‖=1 ∧
    IsGreatest {r : ℝ | ∃ a b : J, ‖a‖=1 ∧ ‖b‖=1 ∧ r=‖S a b‖} (Real.sqrt 2) ∧
    IsGreatest {r : ℝ | ∃ a b : J, ‖a‖=1 ∧ ‖b‖=1 ∧ r=‖D t a b‖}
      (Real.sqrt (1+t^2)) ∧
    IsGreatest {r : ℝ | ∃ i j k : Fin 4, r=‖curvature i j k‖} 1 := by
  refine ⟨by simp [e], ⟨⟨balanced,balanced,balanced_norm,balanced_norm,
    spin_attained.symm⟩,?_⟩,
    ⟨⟨extremalLabel t,e 1,extremal_norm t,by simp [e],(d_attained t).symm⟩,?_⟩,
    ⟨⟨1,2,2,curvature_attained.symm⟩,?_⟩⟩
  · rintro r ⟨a,b,ha,hb,rfl⟩
    simpa [ha,hb] using spin_bound a b
  · rintro r ⟨a,b,ha,hb,rfl⟩
    simpa [ha,hb] using d_bound t a b
  · rintro r ⟨i,j,k,rfl⟩
    exact curvature_bound i j k

/-- The actual label Gram, distinct from the action Gram. -/
def labelGram (t : ℝ) : J →ₗ[ℝ] J :=
  ∑ i : Fin 4, (LinearMap.adjoint ((LinearMap.flip (D t)) (e i))).comp
    ((LinearMap.flip (D t)) (e i))

private theorem label_gram_coordinates (t : ℝ) (a : J) :
    labelGram t a=toLp 2 ![2*t^2*a 0+2*t*a 3,2*a 1,2*a 2,2*t*a 0+2*a 3] := by
  apply ext_inner_right ℝ
  intro b
  simp [labelGram,inner_sum,LinearMap.adjoint_inner_left,PiLp.inner_apply,
    D,C,cross,cross_apply,shift,e,PiLp.single_apply,Fin.sum_univ_succ,RCLike.inner_apply]
  <;> ring

private theorem label_eigenvalues (t lam : ℝ) :
    (∃ a : J, a≠0 ∧ labelGram t a=lam • a) ↔
      lam=0 ∨ lam=2 ∨ lam=2*(1+t^2) := by
  constructor
  · rintro ⟨a,ha,heq⟩
    by_cases h0 : lam=0
    · exact Or.inl h0
    by_cases h2 : lam=2
    · exact Or.inr (Or.inl h2)
    by_cases hp : lam=2*(1+t^2)
    · exact Or.inr (Or.inr hp)
    exfalso
    have hx := congrArg (fun v : J => v 0) heq
    have hz := congrArg (fun v : J => v 3) heq
    simp [label_gram_coordinates] at hx hz
    have hc : lam*(lam-2*(1+t^2))≠0 :=
      mul_ne_zero h0 (sub_ne_zero.mpr hp)
    have ha0 : a 0=0 := by
      have hh : (lam*(lam-2*(1+t^2)))*a 0=0 := by
        linear_combination -(lam-2)*hx-2*t*hz
      exact (mul_eq_zero.mp hh).resolve_left hc
    have ha3 : a 3=0 := by
      have hh : (lam*(lam-2*(1+t^2)))*a 3=0 := by
        linear_combination -2*t*hx-(lam-2*t^2)*hz
      exact (mul_eq_zero.mp hh).resolve_left hc
    apply ha
    ext i; fin_cases i
    · exact ha0
    · have hh := congrArg (fun v : J => v 1) heq
      simp [label_gram_coordinates] at hh
      have hp : (2-lam)*a 1=0 := by nlinarith
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (Ne.symm h2))
    · have hh := congrArg (fun v : J => v 2) heq
      simp [label_gram_coordinates] at hh
      have hp : (2-lam)*a 2=0 := by nlinarith
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (Ne.symm h2))
    · exact ha3
  · rintro (rfl|rfl|rfl)
    · refine ⟨e 0-t • e 3,?_,?_⟩
      · intro h
        have hh := congrArg (fun a : J => a 0) h
        norm_num [e,PiLp.single_apply] at hh
      · ext i; fin_cases i <;> simp [label_gram_coordinates,e,PiLp.single_apply] <;> ring
    · refine ⟨e 1,by simp [e],?_⟩
      ext i; fin_cases i <;> simp [label_gram_coordinates,e,PiLp.single_apply]
    · refine ⟨t • e 0+e 3,?_,?_⟩
      · intro h
        have hh := congrArg (fun a : J => a 3) h
        norm_num [e,PiLp.single_apply] at hh
      · ext i; fin_cases i <;> simp [label_gram_coordinates,e,PiLp.single_apply] <;> ring

/-- The positive spectrum of the actual action Gram. -/
def positiveActionSpectrum (t : ℝ) : Set ℝ :=
  {lam : ℝ | 0<lam ∧ ∃ a : J, a≠0 ∧ actionGram t a=lam • a}
/-- The square root of the actual least positive action eigenvalue. -/
def actionGap (t : ℝ) : ℝ := Real.sqrt (sInf (positiveActionSpectrum t))

private theorem minimum_positive (t : ℝ) : IsLeast (positiveActionSpectrum t) 2 := by
  refine ⟨⟨by norm_num,?_⟩,?_⟩
  · exact (gram_eigenvalues t 2).2 (Or.inr (Or.inr rfl))
  · rintro lam ⟨hpos,heig⟩
    rcases (gram_eigenvalues t lam).1 heig with h|h|h
    · linarith
    · rw [h]; positivity
    · linarith

/-- Both exact spectra and the actual positive square-root gap belong to the same local action. -/
theorem exact_label_data (t : ℝ) :
    (∀ a : J, labelGram t a=toLp 2 ![2*t^2*a 0+2*t*a 3,2*a 1,2*a 2,2*t*a 0+2*a 3]) ∧
    (∀ lam : ℝ, (∃ a : J, a≠0 ∧ labelGram t a=lam • a) ↔
      lam=0 ∨ lam=2 ∨ lam=2*(1+t^2)) ∧
    IsLeast (positiveActionSpectrum t) 2 ∧ actionGap t=Real.sqrt 2 := by
  refine ⟨label_gram_coordinates t,label_eigenvalues t,minimum_positive t,?_⟩
  unfold actionGap
  rw [(minimum_positive t).csInf_eq]

/-- The common kernel of the actual complete action table. -/
def commonFixed (t : ℝ) : Submodule ℝ J := ⨅ i : Fin 4, (D t (e i)).ker

private theorem fixed_mem (t : ℝ) (a : J) :
    a∈commonFixed t ↔ ∃ r : ℝ, a=r • e 0 := by
  simp only [commonFixed,Submodule.mem_iInf,LinearMap.mem_ker]
  exact (common_kernel t a).trans (scalar_axis a)

private theorem support_orthogonal (t : ℝ) (a : J) :
    a∈(commonFixed t).orthogonal ↔ a 0=0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    have he0 : e 0∈commonFixed t := (fixed_mem t (e 0)).2 ⟨1,by simp⟩
    have hh := h (e 0) he0
    simpa [e,EuclideanSpace.inner_single_left] using hh
  · intro ha b hb
    rcases (fixed_mem t b).1 hb with ⟨r,rfl⟩
    simp [e,EuclideanSpace.inner_single_left,ha]

private theorem spectral_lower (t : ℝ) (a : J) (ha : a∈actionSupport t) :
    2*‖a‖^2≤inner ℝ a (actionGram t a) := by
  have h0 := (support_coordinates t a).1 ha
  have heq : inner ℝ a (actionGram t a)=2*‖a‖^2+t^2*(a 1^2+a 2^2) := by
    simp [gram_coordinates,PiLp.inner_apply,EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succ,RCLike.inner_apply,h0]
    <;> ring
  rw [heq]
  positivity

/-- The positive support has an attained uniform gap, and the label and action kernels differ. -/
theorem exact_support_gap (t : ℝ) :
    actionSupport t=(commonFixed t).orthogonal ∧
    (∀ a : J, a∈actionSupport t → 2*‖a‖^2≤inner ℝ a (actionGram t a)) ∧
    (e 3∈actionSupport t ∧ ‖e 3‖=1 ∧ actionGram t (e 3)=2 • e 3) ∧
    D t≠0 ∧
    (t≠0 → (∃ a : J, D t a a≠0) ∧ D t (e 0)≠0 ∧
      (D t).ker≠commonFixed t) ∧
    (∀ a : J, D 0 a a=0) ∧ D 0 (e 0)=0 := by
  refine ⟨?_,spectral_lower t,⟨?_,by simp [e],?_⟩,?_,?_,?_,?_⟩
  · ext a
    exact (support_coordinates t a).trans (support_orthogonal t a).symm
  · exact (support_coordinates t (e 3)).2 (by simp [e,PiLp.single_apply])
  · ext i; fin_cases i <;> simp [gram_coordinates,e,PiLp.single_apply]
  · intro h
    have he := congrArg (fun F : J →ₗ[ℝ] J →ₗ[ℝ] J => F (e 1) (e 2)) h
    have he3 : D t (e 1) (e 2)=e 3 := by
      ext i; fin_cases i <;> norm_num [D,C,cross,cross_apply,shift,e,PiLp.single_apply]
    rw [he3] at he
    have hh := congrArg (fun a : J => a 3) he
    norm_num [e,PiLp.single_apply] at hh
  · intro ht
    have hp : 0<|t| := abs_pos.mpr ht
    have hself : D t balanced balanced≠0 := by
      intro h
      have hh := self_attained t
      rw [h,norm_zero] at hh
      linarith
    have hunit : D t (e 0)≠0 := by
      intro h
      have hh := unit_attained t
      rw [h,LinearMap.zero_apply,norm_zero] at hh
      linarith
    refine ⟨⟨balanced,hself⟩,hunit,?_⟩
    intro hk
    have hmem : e 0∈commonFixed t := (fixed_mem t (e 0)).2 ⟨1,by simp⟩
    rw [←hk] at hmem
    exact hunit hmem
  · intro a
    ext i; fin_cases i <;> simp [D,C,cross,cross_apply,shift] <;> ring
  · apply LinearMap.ext
    intro a
    ext i; fin_cases i <;> simp [D,C,cross,cross_apply,shift,e,PiLp.single_apply]

end D5.S3.Quantum.Algebra.PauliFixedProductFamily
