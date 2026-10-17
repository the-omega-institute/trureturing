import Reg.Support.FibonacciQuadratic
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.IntervalCases

namespace Reg.Support.FibonacciL22
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open Reg.Support.FibonacciQuadratic
open _root_.Set
open scoped Topology
noncomputable section

def P : List Label :=
  [.L2, .L2, .L0, .L3, .L3, .L5, .L0, .L3,
   .L5, .L5, .L3, .L2, .L2, .L5, .L0, .L3,
   .L0, .L3, .L3, .L5, .L5, .L3]
def Q : List Label :=
  [.L2, .L5, .L0, .L0, .L3, .L0, .L3, .L3,
   .L5, .L5, .L3, .L2, .L2, .L0, .L3, .L3,
   .L5, .L0, .L3, .L5, .L5, .L3]
def R : List Label :=
  [.L2, .L2, .L0, .L3, .L3, .L5, .L0, .L3,
   .L5, .L5, .L3, .L2, .L5, .L0, .L0, .L3,
   .L0, .L3, .L3, .L5, .L5, .L3]
def h : List Color :=
  [3, 3, 1, 1, 0, 2, 1, 0,
   2, 3, 0, 3, 3, 2, 1, 0,
   2, 1, 0, 2, 3, 0]
def j : List Color :=
  [3, 3, 1, 1, 0, 2, 1, 0,
   2, 3, 0, 3, 3, 1, 1, 0,
   2, 1, 0, 2, 3, 0]
def U : Bool → List Label := fun i => if i then R else P
def V : Bool → List Label := fun _ => Q
def W : Bool → List Color := fun i => if i then j else h
def ownership : Ownership := fun _ => false
def theta : ℝ := eval ((-14597579/19702990 : ℚ), (24837069/19702990 : ℚ))
def lo : ℝ := eval ((3152047/7881196 : ℚ), (2358781/3940598 : ℚ))
def hi : ℝ := eval ((788009/1970299 : ℚ), (1179395/1970299 : ℚ))
def b : ℝ := eval ((3940271/7881196 : ℚ), (1300303/1970299 : ℚ))

theorem legal_words : LegalWord .G0 .G0 P ∧ LegalWord .G0 .G0 Q ∧
    (∀ i, LegalWord .G0 .G0 (U i)) ∧ (∀ i, LegalWord .G0 .G0 (V i)) := by
  simp only [U, V]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro i; cases i <;> rfl
  · intro i; rfl

theorem lengths : P.length = h.length ∧ Q.length = h.length ∧
    (∀ i, (U i).length = 22) ∧ (∀ i, (V i).length = 22) ∧
    (∀ i, (U i).length = (W i).length) := by
  decide

theorem different_returns : U false ≠ U true := by decide

theorem stem : 1 < P.length ∧
    (∀ p (hp : p < 1), P[p]'(by simp [P]; omega) = Q[p]'(by simp [Q]; omega)) ∧
    P[1] ≠ Q[1] := by
  refine ⟨by decide, ?_, by decide⟩
  intro p hp
  have : p = 0 := by omega
  subst p
  rfl

theorem positive_slope : 0 < (-g)^22 := by
  have hg : 0 < g := tail_arithmetic.2.2.2.1
  rw [show (22 : ℕ) = 2*11 by decide, pow_mul]
  exact pow_pos (sq_pos_of_ne_zero (neg_ne_zero.mpr (ne_of_gt hg))) _

theorem theta_bounds : 0 < theta ∧ theta < lam := by
  have h := t_bounds
  norm_num [theta, eval, lam, T2]
  constructor <;> linarith [h.1,h.2]

theorem slope_value : (-g)^22 = eval (17167680177565, -27777890035288) := by
  have h := eval_power (1,-2) 22
  norm_num [power, mul] at h
  rw [h]
  congr 1
  simp [eval, g]
  ring

theorem p_translation : compose P 0 = eval (9761370294116, -15794228912652) := by
  have h := compose_eval P (0,0)
  norm_num [P, composePair, step, shiftPair, eval] at h ⊢
  exact h

theorem q_translation : compose Q 0 = eval (9748949606797, -15774131818406) := by
  have h := compose_eval Q (0,0)
  norm_num [Q, composePair, step, shiftPair, eval] at h ⊢
  exact h

theorem r_translation : compose R 0 = eval (9761282890313, -15794087490328) := by
  have h := compose_eval R (0,0)
  norm_num [R, composePair, step, shiftPair, eval] at h ⊢
  exact h

theorem endpoints : canonicalReturnLo U 22 = lo ∧ canonicalReturnHi U 22 = hi ∧
    canonicalReturnLo V 22 = b ∧ canonicalReturnHi V 22 = b := by
  have ht := tail_arithmetic.1
  have bounds := t_bounds
  have order : compose R 0 ≤ compose P 0 := by
    rw [p_translation, r_translation]
    norm_num [eval]
    linarith [bounds.1,bounds.2]
  have den : 1 - (-g)^22 ≠ 0 := ne_of_gt (by
    have h := (return_slope_control 22 (by decide)).2.1
    linarith)
  simp only [canonicalReturnLo, canonicalReturnHi, canonicalAffineLo, canonicalAffineHi,
    if_pos positive_slope, U, V, Bool.false_eq_true, if_false, if_true,
    min_eq_right order, max_eq_left order, min_self, max_self]
  rw [p_translation, r_translation, q_translation]
  rw [slope_value] at den ⊢
  constructor
  · apply (div_eq_iff den).mpr
    norm_num [lo, eval]
    nlinarith [ht]
  constructor
  · apply (div_eq_iff den).mpr
    norm_num [hi, eval]
    nlinarith [ht]
  constructor <;> apply (div_eq_iff den).mpr <;>
    norm_num [b, eval] <;> nlinarith [ht]


#print axioms theta_bounds
#print axioms endpoints
end
end Reg.Support.FibonacciL22
