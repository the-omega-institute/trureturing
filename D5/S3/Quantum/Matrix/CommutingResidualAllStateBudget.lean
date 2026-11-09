/- GID: D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/CommutingResidualAllStateBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/NonsingularPencilStateBudget]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim; result=D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.result; claim=D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim
   digest: A fixed four-dimensional table with a commuting nonzero residual and all-state strict budget. -/

import D5.S3.Quantum.Matrix.NonsingularPencilStateBudget

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
private def pencil (p q : ℝ) : A :=
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
  norm_num [hs4]

private def f (w : ℂ) : ℂ := w^4+2*w^2+3

private theorem determinant_certificate (p q : ℝ) :
    (pencil p q).det =
      (Complex.normSq (f ((p:ℂ)-q*Complex.I)) + 4*q^2 -
        q^2/32*((p^2+q^2+3)^2+4*p^2+2) + q^4/4096 : ℝ) := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast sqrt_two_sq
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast sqrt_two_ne
  simp [pencil,NonsingularPencilStateBudget.pencil,Matrix.det_succ_row_zero,
    Matrix.det_fin_three,Matrix.det_fin_two,Matrix.submatrix_apply,
    h,x,r,c,k,t,z,g,eta,Matrix.mul_apply,Fin.sum_univ_succ,Fin.succAbove,Matrix.one_apply,
    f,Complex.normSq_apply,Complex.conj_ofReal,Complex.conj_I,map_div₀,map_sub,map_one]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.div_re,
    Complex.div_im,Complex.normSq_apply,Complex.I_re,Complex.I_im,←Complex.ofReal_pow]
  all_goals simp only [←Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im]
  all_goals field_simp
  all_goals ring_nf
  all_goals norm_num [show (4:ℕ)=2*2 from rfl, show (6:ℕ)=2*3 from rfl, show (8:ℕ)=2*4 from rfl, pow_mul, sqrt_two_sq]
  all_goals ring

private theorem determinant_positive (p q : ℝ) : 0 < (pencil p q).det.re := by
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

/-- The exact pencil is positive on the entire real parameter plane. -/
private theorem all_state_budget (φ : A →ₚ[ℂ] ℂ) (hm : 0 < (φ 1).re) :
    (φ g).re^2+(φ k).re^2 < (φ 1).re*(φ (x*x)).re := by
  rcases table_equations with ⟨_,_,_,_,_,_,_,_,_,_,_,hkH,hgH⟩
  apply (NonsingularPencilStateBudget.strict_budget (x*x) k g x_squared_posDef
    hkH hgH (fun p q => ?_) φ).2.2.2.1 hm
  change (pencil p q).det ≠ 0
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
      change (pencil p q).det = 0 at hz
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

end D5.S3.Quantum.Matrix.CommutingResidualAllStateBudget
