/- GID: D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/CommutingResidualAllStateBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim; result=D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.result; claim=D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim
   digest: A fixed four-dimensional table with a commuting nonzero residual and all-state strict budget. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

/-
The compact-sphere proof in quadratic_positive_open is adapted from
TauCetiProject/TauCeti, commit 8c1eaed7cd02e6fee2db1f66783fb8f03025d76d,
TauCeti/Analysis/Matrix/PosDef.lean, isOpen_setOfPred_re_dotProduct_pos.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude.
Replace this transplanted helper by a direct upstream application when the
pinned Mathlib supplies its equivalent statement.
-/

noncomputable section
open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.NonsingularPencilStateBudget

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem quadratic_positive_open :
    IsOpen {M : Matrix n n ℂ | ∀ x : n → ℂ, x ≠ 0 →
      0 < (star x ⬝ᵥ M *ᵥ x).re} := by
  rw [isOpen_iff_mem_nhds]
  intro M hM
  have key : ∀ᶠ N in 𝓝 M, ∀ x ∈ Metric.sphere (0 : n → ℂ) 1,
      0 < (star x ⬝ᵥ N *ᵥ x).re := by
    refine (isCompact_sphere (0 : n → ℂ) 1).eventually_forall_of_forall_eventually
      fun y hy => ?_
    have hcont : Continuous fun z : Matrix n n ℂ × (n → ℂ) =>
        (star z.2 ⬝ᵥ z.1 *ᵥ z.2).re := by fun_prop
    exact (hcont.tendsto (M, y)).eventually_const_lt
      (hM y (ne_zero_of_mem_sphere one_ne_zero ⟨y, hy⟩))
  filter_upwards [key] with N hN x hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h := hN (‖x‖⁻¹ • x) (by simp [norm_smul, hx0.ne'])
  simp only [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul] at h
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hx0)).mp
    ((mul_pos_iff_of_pos_left (inv_pos.mpr hx0)).mp h)

private theorem connected_posDef {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (P : X → Matrix n n ℂ) (hP : Continuous P)
    (hH : ∀ a, (P a).IsHermitian) (hdet : ∀ a, (P a).det ≠ 0)
    (a₀ : X) (h₀ : (P a₀).PosDef) : ∀ a, (P a).PosDef := by
  have hc : IsClosed {a | (P a).PosDef} := by
    have heq : {a | (P a).PosDef} = {a | (P a).PosSemidef} := by
      ext a
      exact ⟨fun h => h.posSemidef, fun h => h.posDef_iff_det_ne_zero.mpr (hdet a)⟩
    rw [heq]
    exact Matrix.posSemidef_is_closed.preimage hP
  have ho : IsOpen {a | (P a).PosDef} := by
    convert quadratic_positive_open.preimage hP using 1
    ext a
    constructor
    · exact fun h x hx => h.re_dotProduct_pos hx
    · intro h
      exact Matrix.PosDef.of_dotProduct_mulVec_pos (hH a) fun x hx =>
        RCLike.pos_iff.mpr ⟨h x hx, (hH a).im_star_dotProduct_mulVec_self x⟩
  have hu := (IsClopen.eq_univ ⟨hc, ho⟩ ⟨a₀, h₀⟩)
  intro a
  have : a ∈ {a | (P a).PosDef} := by rw [hu]; trivial
  exact this

/-- The same matrix algebra carries every parameter and every positive reading. -/
def pencil (E K G : Matrix n n ℂ) (p q : ℝ) : Matrix n n ℂ :=
  E + (p ^ 2 + q ^ 2) • 1 - (2 * p) • K - (2 * q) • G

private theorem positive_reading {A : Matrix n n ℂ} (hA : A.PosDef)
    (φ : Matrix n n ℂ →ₚ[ℂ] ℂ) (hm : 0 < (φ 1).re) : 0 < (φ A).re := by
  haveI : Nonempty n := by
    by_contra h
    haveI : IsEmpty n := not_nonempty_iff.mp h
    have : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
    simpa [this] using hm
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff A hA.isHermitian).mpr
    (fun x hx => hA.isStrictlyPositive.spectrum_pos hx)
  have hh := φ.monotone hle
  have hre := Complex.le_def.mp hh |>.1
  change (φ (algebraMap ℝ (Matrix n n ℂ) r)).re ≤ (φ A).re at hre
  simp only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    map_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hre
  exact (mul_pos hr hm).trans_le hre

/-- Nonsingularity on the whole real plane, together with positivity at the origin,
forces a strict homogeneous budget for every positive complex-linear functional. -/
private theorem positive_mass_budget (E K G : Matrix n n ℂ) (hE : E.PosDef)
    (hK : K.IsHermitian) (hG : G.IsHermitian)
    (hdet : ∀ p q : ℝ, (pencil E K G p q).det ≠ 0)
    (φ : Matrix n n ℂ →ₚ[ℂ] ℂ) (hm : 0 < (φ 1).re) :
    (φ G).re ^ 2 + (φ K).re ^ 2 < (φ 1).re * (φ E).re := by
  let P : ℝ × ℝ → Matrix n n ℂ := fun a => pencil E K G a.1 a.2
  have hP : Continuous P := by unfold P pencil; fun_prop
  have hH (a : ℝ × ℝ) : (P a).IsHermitian :=
    ((hE.isHermitian.add ((isHermitian_one : (1 : Matrix n n ℂ).IsHermitian).smul
      (IsSelfAdjoint.all _))).sub (hK.smul (IsSelfAdjoint.all _))).sub
      (hG.smul (IsSelfAdjoint.all _))
  have h₀ : (P (0, 0)).PosDef := by simpa [P, pencil] using hE
  have hpos := connected_posDef P hP hH (fun a => hdet a.1 a.2) (0, 0) h₀
  have hh := positive_reading (hpos ((φ K).re / (φ 1).re, (φ G).re / (φ 1).re)) φ hm
  simp only [P, pencil, map_sub, map_add, ← Complex.coe_smul, map_smul,
    smul_eq_mul, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
  have hm0 := ne_of_gt hm
  field_simp at hh
  nlinarith [sq_nonneg ((φ G).re), sq_nonneg ((φ K).re)]

/-- All positive complex-linear functionals retain their mass, including the zero
functional. Hermitian readings are real; every positive mass gives strictness. -/
theorem strict_budget (E K G : Matrix n n ℂ) (hE : E.PosDef)
    (hK : K.IsHermitian) (hG : G.IsHermitian)
    (hdet : ∀ p q : ℝ, (pencil E K G p q).det ≠ 0)
    (φ : Matrix n n ℂ →ₚ[ℂ] ℂ) :
    (φ E).im = 0 ∧ (φ K).im = 0 ∧ (φ G).im = 0 ∧
    (0 < (φ 1).re →
      (φ G).re ^ 2 + (φ K).re ^ 2 < (φ 1).re * (φ E).re) ∧
    ((φ 1).re = 0 → φ = 0 ∧
      (φ G).re ^ 2 + (φ K).re ^ 2 = (φ 1).re * (φ E).re) := by
  refine ⟨(Complex.im_eq_zero_iff_isSelfAdjoint (φ E)).mpr
      ((Matrix.isHermitian_iff_isSelfAdjoint.mp hE.isHermitian).map' φ),
    (Complex.im_eq_zero_iff_isSelfAdjoint (φ K)).mpr
      ((Matrix.isHermitian_iff_isSelfAdjoint.mp hK).map' φ),
    (Complex.im_eq_zero_iff_isSelfAdjoint (φ G)).mpr
      ((Matrix.isHermitian_iff_isSelfAdjoint.mp hG).map' φ),
    positive_mass_budget E K G hE hK hG hdet φ, ?_⟩
  intro hm
  let f : Matrix n n ℂ →P[ℂ] ℂ := PositiveContinuousLinearMap.ofClass φ
  have hunit : φ 1 = 0 := by
    apply Complex.ext hm
    exact (Complex.le_def.mp (φ.map_nonneg (show (0 : Matrix n n ℂ) ≤ 1 from zero_le_one))).2.symm
  have hnorm : ‖f.toContinuousLinearMap‖ = 0 := by
    have hh := f.ofReal_opNorm_eq_map_one
    have h := congrArg Complex.re hh
    change ‖f.toContinuousLinearMap‖ = (φ 1).re at h
    exact h.trans hm
  have hφ : φ = 0 := by
    ext a
    have hb := f.toContinuousLinearMap.le_opNorm a
    rw [hnorm, zero_mul] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  exact ⟨hφ, by simp [hφ]⟩

#print axioms strict_budget

end D5.S3.Quantum.Matrix.NonsingularPencilStateBudget

end

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.CommutingResidualAllStateBudget

private abbrev A := Matrix (Fin 4) (Fin 4) ℂ
private def eta : ℂ := (1 - Complex.I) / (Real.sqrt 2 : ℂ)
private def h : A := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]
private def c : A := !![1,0,0,0; 0,-1,0,0; 0,0,-1,0; 0,0,0,1]
private def x : A := !![1,0,1,eta; 0,-1,eta,1; 1,star eta,-1,0; star eta,1,0,1]
private def r : A := (1/16 : ℝ) • c
private def z : A := (1/2 : ℝ) • (x - h*x*h)
private def k : A := h*c
private def t : A := Complex.I • (h*z)
private def g : A := t+r
private def jordan (a b : A) : A := (1/2 : ℝ) • (a*b+b*a)
private def concretePencil (p q : ℝ) : A :=
  NonsingularPencilStateBudget.pencil (x*x) k g p q

private theorem sqrt_two_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
private theorem sqrt_two_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))

private theorem table_equations :
    h.IsHermitian ∧ x.IsHermitian ∧ r.IsHermitian ∧
    h*h=1 ∧ c=(1/2 : ℝ) • (x+h*x*h) ∧ k=jordan h x ∧
    t=(Complex.I/2) • (h*x-x*h) ∧ h*r=r*h ∧ c*r=r*c ∧
    r*r=(1/256 : ℝ) • (1:A) ∧
    jordan z r * jordan z r=(1/256 : ℝ) • (1:A) ∧ k.IsHermitian ∧ g.IsHermitian := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast sqrt_two_sq
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast sqrt_two_ne
  repeat' constructor
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j
  all_goals simp [Matrix.IsHermitian, Matrix.conjTranspose_apply, h,x,r,c,k,t,z,g,jordan,
    eta, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Complex.conj_ofReal,
    Complex.conj_I, map_div₀, map_sub, map_one]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp_all [hs]
  all_goals norm_num

private theorem det_x : x.det = 3 := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast sqrt_two_sq
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast sqrt_two_ne
  simp [Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Fin.sum_univ_succ, Fin.succAbove, x, eta, Matrix.submatrix_apply, Complex.conj_ofReal,
    Complex.conj_I, map_div₀, map_sub, map_one]
  field_simp
  ring_nf
  have hs4 : (Real.sqrt 2 : ℂ)^4 = 4 := by calc
    _ = ((Real.sqrt 2 : ℂ)^2)^2 := by ring
    _ = 4 := by rw [hs]; norm_num
  norm_num [hs4,hs]

private def f (w : ℂ) : ℂ := w^4+2*w^2+3

private theorem determinant_certificate (p q : ℝ) :
    (concretePencil p q).det =
      (Complex.normSq (f ((p:ℂ)-q*Complex.I)) + 4*q^2 -
        q^2/32*((p^2+q^2+3)^2+4*p^2+2) + q^4/4096 : ℝ) := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast sqrt_two_sq
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast sqrt_two_ne
  have hr4 : Real.sqrt 2 ^ 4 = 4 := by
    calc
      _ = (Real.sqrt 2 ^ 2)^2 := by ring
      _ = 4 := by rw [sqrt_two_sq]; norm_num
  have hr6 : Real.sqrt 2 ^ 6 = 8 := by
    calc
      _ = (Real.sqrt 2 ^ 2)^3 := by ring
      _ = 8 := by rw [sqrt_two_sq]; norm_num
  have hr8 : Real.sqrt 2 ^ 8 = 16 := by
    calc
      _ = (Real.sqrt 2 ^ 2)^4 := by ring
      _ = 16 := by rw [sqrt_two_sq]; norm_num
  simp [concretePencil,NonsingularPencilStateBudget.pencil,Matrix.det_succ_row_zero,
    Matrix.det_fin_three,Matrix.det_fin_two,Matrix.submatrix_apply,
    h,x,r,c,k,t,z,g,eta,Matrix.mul_apply,Fin.sum_univ_succ,Fin.succAbove,Matrix.one_apply,
    f,Complex.normSq_apply,Complex.conj_ofReal,Complex.conj_I,map_div₀,map_sub,map_one]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.div_re,
    Complex.div_im,Complex.normSq_apply,Complex.I_re,Complex.I_im,pow_succ]
  all_goals try simp only [←Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im]
  all_goals field_simp
  all_goals ring_nf
  all_goals norm_num [hr4,hr6,hr8,sqrt_two_sq]
  all_goals ring

private theorem determinant_positive (p q : ℝ) : 0 < (concretePencil p q).det.re := by
  rw [determinant_certificate]
  simp only [Complex.ofReal_re]
  let s := p^2+q^2
  let w : ℂ := (p:ℂ)-q*Complex.I
  have hs0 : 0 ≤ s := add_nonneg (sq_nonneg p) (sq_nonneg q)
  have hp : p^2 ≤ s := le_add_of_nonneg_right (sq_nonneg q)
  have hq : q^2 ≤ s := le_add_of_nonneg_left (sq_nonneg p)
  have hf0 : 0 ≤ Complex.normSq (f w) := Complex.normSq_nonneg _
  have hq4 : 0 ≤ q^4 := by positivity
  change 0 < Complex.normSq (f w)+4*q^2-q^2/32*((s+3)^2+4*p^2+2)+q^4/4096
  by_cases hs : s ≤ 6
  · have hb : (s+3)^2+4*p^2+2 ≤ 107 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs)]
    have hmul := mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hb)
    by_cases hq0 : q=0
    · subst q
      have hf : 0 < Complex.normSq (f ((p:ℂ)-0*Complex.I)) := by
        have hp : (0:ℝ) < p^4+2*p^2+3 := by positivity
        have he : f ((p:ℂ)-0*Complex.I) = (p^4+2*p^2+3 : ℝ) := by simp [f]
        rw [he,Complex.normSq_ofReal]
        exact mul_pos hp hp
      simpa [w] using hf
    · have hqpos := sq_pos_of_ne_zero hq0
      nlinarith
  · have hs6 : 6 ≤ s := le_of_lt (lt_of_not_ge hs)
    have hn : ‖w‖^2=s := by
      rw [←Complex.normSq_eq_norm_sq]
      simp [w,Complex.normSq_apply,s]
      ring
    have hn4 : ‖w^4‖=s^2 := by rw [norm_pow,show 4=2*2 from rfl,pow_mul,hn]
    have hnorm : s^2 ≤ ‖f w‖+2*s+3 := by
      calc
        s^2 = ‖f w-(2*w^2+3)‖ := by
          rw [show f w-(2*w^2+3)=w^4 by unfold f; ring,hn4]
        _ ≤ ‖f w‖+‖2*w^2+3‖ := norm_sub_le _ _
        _ ≤ ‖f w‖+(‖(2:ℂ)*w^2‖+‖(3:ℂ)‖) := by gcongr; exact norm_add_le _ _
        _ = ‖f w‖+2*s+3 := by simp [norm_mul,norm_pow,hn]; ring
    have hl : s^2/2 ≤ ‖f w‖ := by nlinarith [sq_nonneg (s-6)]
    have hf : s^4/4 ≤ Complex.normSq (f w) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [sq_nonneg (‖f w‖-s^2/2)]
    have hb : (s+3)^2+4*p^2+2 ≤ 3*s^2 := by nlinarith [sq_nonneg (s-6)]
    have hprod : q^2/32*((s+3)^2+4*p^2+2) ≤ s/32*(3*s^2) :=
      mul_le_mul (by linarith) hb (by positivity) (by positivity)
    have hfinal : 0 < s^4/4-3*s^3/32 := by
      have hs3 : 0 < s^3 := pow_pos (by linarith) _
      have hm := mul_pos hs3 (show 0 < s/4-3/32 by linarith)
      nlinarith
    nlinarith

private theorem x_squared_posDef : (x*x).PosDef := by
  have hxi : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).mpr (by rw [det_x]; norm_num)
  have hxinj : Function.Injective x.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hxi
  simpa only [show xᴴ=x from table_equations.2.1] using
    Matrix.PosDef.conjTranspose_mul_self x hxinj

/-- The exact concretePencil is positive on the entire real parameter plane. -/
private theorem all_state_budget (φ : A →ₚ[ℂ] ℂ) (hm : 0 < (φ 1).re) :
    (φ g).re^2+(φ k).re^2 < (φ 1).re*(φ (x*x)).re := by
  rcases table_equations with ⟨_,_,_,_,_,_,_,_,_,_,_,hkH,hgH⟩
  apply (NonsingularPencilStateBudget.strict_budget (x*x) k g x_squared_posDef
    hkH hgH (fun p q => ?_) φ).2.2.2.1 hm
  change (concretePencil p q).det ≠ 0
  intro hz
  have hh := determinant_positive p q
  rw [hz] at hh
  norm_num at hh

/-- The original fixed table retains every positive complex-linear reading and
both mass boundaries, together with the exact nonzero residual squares. -/
theorem witness :
    h.IsHermitian ∧ x.IsHermitian ∧ r.IsHermitian ∧ h*h=1 ∧
    c=(1/2 : ℝ) • (x+h*x*h) ∧ k=jordan h x ∧
    t=(Complex.I/2) • (h*x-x*h) ∧ h*r=r*h ∧ c*r=r*c ∧
    r*r=(1/256 : ℝ) • (1:A) ∧
    jordan z r*jordan z r=(1/256 : ℝ) • (1:A) ∧
    (∀ φ : A →ₚ[ℂ] ℂ,
      (φ (x*x)).im=0 ∧ (φ k).im=0 ∧ (φ g).im=0 ∧
      (0 < (φ 1).re → (φ g).re^2+(φ k).re^2<(φ 1).re*(φ (x*x)).re) ∧
      ((φ 1).re=0 → φ=0 ∧
        (φ g).re^2+(φ k).re^2=(φ 1).re*(φ (x*x)).re)) := by
  rcases table_equations with ⟨hh,hx,hr,hh2,hc,hk,ht,hhr,hcr,hrr,hzr,hkH,hgH⟩
  refine ⟨hh,hx,hr,hh2,hc,hk,ht,hhr,hcr,hrr,hzr,?_⟩
  intro φ
  have readings := NonsingularPencilStateBudget.strict_budget (x*x) k g x_squared_posDef
    hkH hgH (fun p q hz => by
      have he := determinant_positive p q
      change (concretePencil p q).det = 0 at hz
      rw [hz] at he
      norm_num at he) φ
  exact ⟨readings.1,readings.2.1,readings.2.2.1,all_state_budget φ,readings.2.2.2.2⟩

def claim : Prop :=
  ∀ H X R : A, H.IsHermitian → X.IsHermitian → R.IsHermitian → H*H=1 →
    let C := (1/2 : ℝ) • (X+H*X*H)
    let K := jordan H X
    let G := (Complex.I/2) • (H*X-X*H)+R
    H*R=R*H → C*R=R*C →
    (∀ φ : A →ₚ[ℂ] ℂ, φ 1=1 → (φ G).re^2+(φ K).re^2<(φ (X*X)).re) → R=0

/-- The two commutators and the all-state strict budget do not force a zero residual. -/
theorem result : ¬ claim := by
  intro hc
  rcases witness with ⟨hh,hx,hr,hh2,hcE,hk,ht,hhr,hcr,hrr,hzr,hread⟩
  have hz : r=0 := hc h x r hh hx hr hh2 hhr
    (by change ((1/2:ℝ) • (x+h*x*h))*r=r*((1/2:ℝ) • (x+h*x*h)); rw [← hcE]; exact hcr) (fun φ hφ => by
      have h := (hread φ).2.2.2.1 (by simp [hφ])
      simpa [← hk,← ht,g,hφ] using h)
  have hh := congrArg (fun M : A => M 0 0) hrr
  norm_num [hz,Matrix.one_apply] at hh

#print axioms witness
#print axioms result

end D5.S3.Quantum.Matrix.CommutingResidualAllStateBudget
