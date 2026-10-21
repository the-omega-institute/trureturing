/- GID: D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.claim; result=D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.result; claim=D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.claim
   digest: A positive definite similarity in dimension seven defeats diagonal majorization. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#18572; Refuted).
Direct frozen dependencies: none (all declarations).
p_sos: proof_shape: bind-only; consumer: p_posDef; escape_witness: none.
p_posDef: proof_shape: bind-only; consumer: result; escape_witness: none.
p_mul_q: proof_shape: bind-only; consumer: p_inv; escape_witness: none.
p_inv: proof_shape: bind-only; consumer: diag_eq; escape_witness: none.
diag_eq: proof_shape: bind-only; consumer: result; escape_witness: none.
v_lower: proof_shape: bind-only; consumer: not_majorizes; escape_witness: none.
not_majorizes: proof_shape: bind-only; consumer: result; escape_witness: none.
Majorizes and claim are the source predicates; p, q, d and v are literal finite data.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
Majorizes retains the doubly-stochastic expression in #18572; the proof uses Mathlib's
Matrix.PosDef, Matrix.inv and doublyStochastic directly.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.UhlmannDiagonalMajorizationRefutation

open _root_.Matrix

/-- `x ≺ y` (`y` majorizes `x`): `x = S y` for a doubly-stochastic matrix `S` (Section 3). -/
def Majorizes {n : ℕ} (y x : Fin n → ℝ) : Prop :=
  ∃ S ∈ doublyStochastic ℝ (Fin n), x = S *ᵥ y

/-- The unrestricted extension discussed in Section 4 of Uhlmann (arXiv:2309.01302): for every
real symmetric positive-definite `P` and every real diagonal `D`, the spectrum of `M = P D P⁻¹`
(the diagonal entries of `D`) is majorized by the diagonal of `M`, in every dimension `n`. -/
def claim : Prop :=
  ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ), P.PosDef → ∀ d : Fin n → ℝ,
    Majorizes (fun i => (P * diagonal d * P⁻¹) i i) d

set_option maxHeartbeats 2000000
private def p : Matrix (Fin 7) (Fin 7) ℝ :=
  !![10,1,2,2,2,2,2;
     1,10,2,2,2,2,2;
     2,2,10,0,0,0,0;
     2,2,0,10,0,0,0;
     2,2,0,0,10,0,0;
     2,2,0,0,0,10,0;
     2,2,0,0,0,0,10]
private noncomputable def q : Matrix (Fin 7) (Fin 7) ℝ :=
  !![8/63,1/63,-1/35,-1/35,-1/35,-1/35,-1/35;
     1/63,8/63,-1/35,-1/35,-1/35,-1/35,-1/35;
     -1/35,-1/35,39/350,2/175,2/175,2/175,2/175;
     -1/35,-1/35,2/175,39/350,2/175,2/175,2/175;
     -1/35,-1/35,2/175,2/175,39/350,2/175,2/175;
     -1/35,-1/35,2/175,2/175,2/175,39/350,2/175;
     -1/35,-1/35,2/175,2/175,2/175,2/175,39/350]
private def d : Fin 7 → ℝ := ![1,20,2,2,2,2,2]
private noncomputable def v : Fin 7 → ℝ := ![64/63,1565/63,36/35,36/35,36/35,36/35,36/35]

private theorem p_sos (x : Fin 7 → ℝ) :
    star x ⬝ᵥ (p *ᵥ x) =
      10 * (∑ i : Fin 5, (x i.succ.succ + (x 0 + x 1)/5)^2) +
      (7/2:ℝ)*(x 0 + x 1)^2 + (9/2:ℝ)*(x 0 - x 1)^2 := by
  simp [p, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

private theorem p_posDef : p.PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
  · rw [isHermitian_iff_isSymm]
    apply IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [p]
  intro x hx
  rw [p_sos]
  have hsq (i : Fin 5) : 0 ≤ (x i.succ.succ + (x 0+x 1)/5)^2 := sq_nonneg _
  have hsum : 0 ≤ ∑ i : Fin 5, (x i.succ.succ + (x 0+x 1)/5)^2 :=
    Finset.sum_nonneg (fun i _ => hsq i)
  have ha := sq_nonneg (x 0+x 1)
  have hb := sq_nonneg (x 0-x 1)
  by_contra h
  have hle := le_of_not_gt h
  have h01 : x 0+x 1 = 0 := by nlinarith
  have h02 : x 0-x 1 = 0 := by nlinarith
  have hx0 : x 0 = 0 := by linarith
  have hx1 : x 1 = 0 := (eq_zero_iff_eq_zero_of_add_eq_zero h01).mp hx0
  have htotal : (∑ i : Fin 5, (x i.succ.succ + (x 0+x 1)/5)^2) = 0 := by nlinarith
  have hz (i : Fin 5) : x i.succ.succ = 0 := by
    simpa only [hx0, hx1, add_zero, zero_div] using
      (Finset.sum_sq_eq_zero_iff (Finset.univ : Finset (Fin 5))
        (fun j => x j.succ.succ + (x 0 + x 1)/5)).mp htotal i (Finset.mem_univ i)
  apply hx
  funext i
  fin_cases i
  · exact hx0
  · exact hx1
  · exact hz 0
  · exact hz 1
  · exact hz 2
  · exact hz 3
  · exact hz 4

private theorem p_mul_q : p * q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [p, q, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

private theorem p_inv : p⁻¹ = q := by
  exact Matrix.inv_eq_right_inv p_mul_q

private theorem diag_eq (i : Fin 7) : (p * diagonal d * p⁻¹) i i = v i := by
  rw [p_inv]
  fin_cases i <;>
    norm_num [p, q, d, v, Matrix.mul_apply, Fin.sum_univ_succ, diagonal_apply, Matrix.vecMul, dotProduct]

private theorem v_lower (i : Fin 7) : (64/63:ℝ) ≤ v i := by
  fin_cases i <;> norm_num [v]

private theorem not_majorizes : ¬ Majorizes v d := by
  rintro ⟨S,hS,heq⟩
  have hbound : (64/63:ℝ) ≤ (S *ᵥ v) 0 := by
    simpa only [Set.mem_Ici, smul_eq_mul, Matrix.mulVec, dotProduct] using
      (convex_Ici (𝕜 := ℝ) (64/63 : ℝ)).sum_mem
        (t := Finset.univ) (w := S 0) (z := v)
        (fun j _ => nonneg_of_mem_doublyStochastic hS)
        (sum_row_of_mem_doublyStochastic hS 0)
        (fun j _ => v_lower j)
  have he := congrFun heq 0
  norm_num [d] at he
  linarith

theorem result : ¬ claim := by
  intro h
  have hm := h 7 p p_posDef d
  have heq : (fun i => (p * diagonal d * p⁻¹) i i) = v := funext diag_eq
  rw [heq] at hm
  exact not_majorizes hm

end D5.S3.Quantum.Matrix.UhlmannDiagonalMajorizationRefutation
