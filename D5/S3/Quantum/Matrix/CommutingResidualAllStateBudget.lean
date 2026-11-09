/- GID: D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/CommutingResidualAllStateBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/NonsingularPencilStateBudget]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim; result=D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.result; claim=D5/S3/Quantum/Matrix/CommutingResidualAllStateBudget.claim
   digest: A fixed four-dimensional table with a commuting nonzero residual and all-state strict budget. -/

import D5.S3.Quantum.Matrix.NonsingularPencilStateBudget

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.CommutingResidualAllStateBudget

abbrev A := Matrix (Fin 4) (Fin 4) ℂ
def eta : ℂ := (1 - Complex.I) / (Real.sqrt 2 : ℂ)
def h : A := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]
def c : A := !![1,0,0,0; 0,-1,0,0; 0,0,-1,0; 0,0,0,1]
def x : A := !![1,0,1,eta; 0,-1,eta,1; 1,star eta,-1,0; star eta,1,0,1]
def r : A := (1/16 : ℝ) • c
def z : A := (1/2 : ℝ) • (x - h*x*h)
def k : A := h*c
def t : A := Complex.I • (h*z)
def g : A := t+r
def jordan (a b : A) : A := (1/2 : ℝ) • (a*b+b*a)
def pencil (p q : ℝ) : A :=
  NonsingularPencilStateBudget.pencil (x*x) k g p q

private theorem sqrt_two_sq : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
private theorem sqrt_two_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))

private theorem table_equations :
    h.IsHermitian ∧ x.IsHermitian ∧ r.IsHermitian ∧
    h*h=1 ∧ c=(1/2 : ℝ) • (x+h*x*h) ∧ k=jordan h x ∧
    t=(Complex.I/2) • (h*x-x*h) ∧ h*r=r*h ∧ c*r=r*c ∧
    r*r=(1/256 : ℝ) • (1:A) ∧
    jordan z r * jordan z r=(1/256 : ℝ) • (1:A) := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast sqrt_two_sq
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast sqrt_two_ne
  repeat' constructor
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j
  all_goals simp [Matrix.IsHermitian, Matrix.conjTranspose_apply, h,x,r,c,k,t,z,jordan,
    eta, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Complex.conj_ofReal,
    Complex.conj_I, map_div₀, map_sub, map_one]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp_all [hs]

private theorem det_x : x.det = 3 := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast sqrt_two_sq
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast sqrt_two_ne
  simp [Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Fin.sum_univ_succ, x, eta, Matrix.submatrix_apply, Complex.conj_ofReal,
    Complex.conj_I, map_div₀, map_sub, map_one]
  field_simp
  ring_nf
  simp_all [hs]

private def f (w : ℂ) : ℂ := w^4+2*w^2+3

private theorem determinant_certificate (p q : ℝ) :
    (pencil p q).det =
      (Complex.normSq (f ((p:ℂ)-q*Complex.I)) + 4*q^2 -
        q^2/32*((p^2+q^2+3)^2+4*p^2+2) + q^4/4096 : ℝ) := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast sqrt_two_sq
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast sqrt_two_ne
  simp [pencil,NonsingularPencilStateBudget.pencil,Matrix.det_succ_row_zero,
    Matrix.det_fin_three,Matrix.det_fin_two,Matrix.submatrix_apply,
    h,x,r,c,k,t,z,g,eta,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply,
    f,Complex.normSq_apply,Complex.conj_ofReal,Complex.conj_I,map_div₀,map_sub,map_one]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,Complex.div_re,
    Complex.div_im,Complex.normSq_apply,Complex.I_re,Complex.I_im]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp_all [sqrt_two_sq]

def claim : Prop :=
  ∀ H X R : A, H.IsHermitian → X.IsHermitian → R.IsHermitian → H*H=1 →
    let C := (1/2 : ℝ) • (X+H*X*H)
    let K := jordan H X
    let G := (Complex.I/2) • (H*X-X*H)+R
    H*R=R*H → C*R=R*C →
    (∀ φ : A →ₚ[ℂ] ℂ, φ 1=1 → (φ G).re^2+(φ K).re^2<(φ (X*X)).re) → R=0

end D5.S3.Quantum.Matrix.CommutingResidualAllStateBudget
