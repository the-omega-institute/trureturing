/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicModFiveMatrixReadout
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Finite F5 matrix powers and normalized traces give uniformly calibrated Frobenius readouts. -/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicModFiveMatrixReadout

abbrev Quad := ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5

def qdet (q : Quad) : ZMod 5 := q.1*q.2.2.2-q.2.1*q.2.2.1
def qtrace (q : Quad) : ZMod 5 := q.1+q.2.2.2
def qmat (q : Quad) : Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  !![q.1,q.2.1;q.2.2.1,q.2.2.2]

theorem det_qmat (q : Quad) : (qmat q).det = qdet q := by
  simp [qmat, qdet, Matrix.det_fin_two_of]

theorem trace_qmat (q : Quad) : (qmat q).trace = qtrace q := by
  simp [qmat, qtrace, Matrix.trace_fin_two_of]

/-- Multiplying determinant-three matrices by two normalizes the observable
trace to the determinant-two convention. -/
def normalizedTrace (q : Quad) : ZMod 5 :=
  if qdet q = 2 then qtrace q else 2*qtrace q

def countTrace (d t : ZMod 5) : ℕ :=
  (Finset.univ.filter (fun q : Quad => qdet q=d ∧ normalizedTrace q=t)).card

def traceCount (t : ZMod 5) : ℕ :=
  if t=2 ∨ t=3 then 30 else 20

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
theorem nonsquare_fibers_normalized_trace :
    (∀ t : ZMod 5, countTrace 2 t = traceCount t) ∧
      (∀ t : ZMod 5, countTrace 3 t = traceCount t) := by decide

def qmul (a b : Quad) : Quad :=
  (a.1*b.1+a.2.1*b.2.2.1,
   a.1*b.2.1+a.2.1*b.2.2.2,
   a.2.2.1*b.1+a.2.2.2*b.2.2.1,
   a.2.2.1*b.2.1+a.2.2.2*b.2.2.2)

def qpow (q : Quad) : ℕ → Quad
  | 0 => (1,0,0,1)
  | n+1 => qmul (qpow q n) q

theorem qmat_mul (q r : Quad) : qmat (qmul q r) = qmat q * qmat r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qmat, qmul, Matrix.mul_apply, Fin.sum_univ_two]

theorem qmat_pow (q : Quad) (n : ℕ) : qmat (qpow q n) = qmat q ^ n := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [qmat, qpow]
  | succ n ih => rw [qpow, qmat_mul, ih, pow_succ]

def IsScalar (q : Quad) : Prop := q.2.1=0 ∧ q.2.2.1=0 ∧ q.1=q.2.2.2
instance (q : Quad) : Decidable (IsScalar q) := by unfold IsScalar; infer_instance

theorem isScalar_qmat (q : Quad) : IsScalar q ↔
    ∃ r : ZMod 5, qmat q = r • (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
  constructor
  · rintro ⟨ha,hb,hc⟩
    refine ⟨q.1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [qmat, ha, hb, hc]
  · rintro ⟨a,h⟩
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp [qmat] at h00 h01 h10 h11
    exact ⟨h01,h10,h00.trans h11.symm⟩

def lengthFromTrace (q : Quad) : ℕ :=
  if qtrace q=0 then 2 else if qtrace q^2=2*qdet q then 4 else 6

private def HasExactProjectiveLength (q : Quad) : Prop :=
  IsScalar (qpow q (lengthFromTrace q)) ∧
    ∀ n : Fin 6, 0 < n.val → n.val < lengthFromTrace q → ¬ IsScalar (qpow q n.val)

private instance (q : Quad) : Decidable (HasExactProjectiveLength q) := by
  unfold HasExactProjectiveLength
  infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
private theorem exact_pow_certificate :
    ∀ q : Quad, qdet q=2 ∨ qdet q=3 → HasExactProjectiveLength q := by decide

/-- For nonsquare determinant, the trace class determines the least
positive matrix power that becomes scalar. -/
theorem exact_nonsquare_projective_length (q : Quad) (h : qdet q=2 ∨ qdet q=3) :
    let k := lengthFromTrace q
    (∃ r : ZMod 5, (qmat q)^k = r • (1:Matrix (Fin 2) (Fin 2) (ZMod 5))) ∧
      ∀ n : ℕ, 0 < n → n < k →
        ¬ ∃ r : ZMod 5, (qmat q)^n = r • (1:Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
  dsimp only
  have hc := exact_pow_certificate q h
  refine ⟨?_,?_⟩
  · rw [← qmat_pow]
    exact (isScalar_qmat _).mp hc.1
  · intro n hn hk
    have h6 : lengthFromTrace q ≤ 6 := by
      unfold lengthFromTrace
      split
      · decide
      · split <;> decide
    rw [← qmat_pow]
    exact fun H => hc.2 ⟨n, lt_of_lt_of_le hk h6⟩ hn hk ((isScalar_qmat _).mpr H)

private def IsNontrivialRepeatedRoot (q : Quad) : Prop :=
  qdet q=1 ∧ qtrace q^2=4 ∧ ¬ IsScalar q

private instance (q : Quad) : Decidable (IsNontrivialRepeatedRoot q) := by
  unfold IsNontrivialRepeatedRoot
  infer_instance

private def ExactFive (q : Quad) : Prop :=
  IsScalar (qpow q 5) ∧
    ∀ n : Fin 5, 0 < n.val → ¬ IsScalar (qpow q n.val)

private instance (q : Quad) : Decidable (ExactFive q) := by
  unfold ExactFive
  infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
private theorem exact_repeated_root_certificate :
    ∀ q : Quad, IsNontrivialRepeatedRoot q → ExactFive q := by decide

/-- The noncentral repeated-root class has actual projective order five. -/
theorem projective_five_of_noncentral_repeated_root (q : Quad)
    (hd : qdet q=1) (ht : qtrace q^2=4) (hn : ¬ IsScalar q) :
    (∃ r : ZMod 5, (qmat q)^5 = r • (1:Matrix (Fin 2) (Fin 2) (ZMod 5))) ∧
      ∀ n : ℕ, 0 < n → n < 5 →
        ¬ ∃ r : ZMod 5, (qmat q)^n = r • (1:Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
  have hc := exact_repeated_root_certificate q ⟨hd,ht,hn⟩
  refine ⟨?_,?_⟩
  · rw [← qmat_pow]
    exact (isScalar_qmat _).mp hc.1
  · intro n hp hn'
    rw [← qmat_pow]
    exact fun H => hc.2 ⟨n,hn'⟩ hp ((isScalar_qmat _).mpr H)

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicModFiveMatrixReadout
