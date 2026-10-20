import Reg.Support.FibonacciFiniteSource
import Reg.Support.FibonacciQuadratic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Reg.Support.FibonacciFiniteCoordinates
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open Reg.Support.FibonacciQuadratic Reg.Support.FibonacciFiniteSource
noncomputable section

/-- Coordinates of finite original sources lie in Z[t], without a fixed word-length bound. -/
def IntegerCoordinate (z : ℝ) : Prop := ∃ a b : ℤ, z = (a : ℝ)+(b : ℝ)*t

private theorem integer_zero : IntegerCoordinate 0 := ⟨0,0,by simp⟩

private theorem integer_branch (l : Label) {z : ℝ} (hz : IntegerCoordinate z) :
    IntegerCoordinate (branch l z) := by
  obtain ⟨a,b,hz⟩ := hz
  have he : z = eval ((a : ℚ),(b : ℚ)) := by simpa [eval] using hz
  rw [he,← eval_step]
  cases l
  · refine ⟨a-2*b,-1-2*a+3*b,?_⟩
    norm_num [eval,step,shiftPair] <;> push_cast <;> ring
  · refine ⟨a-2*b,-2*a+3*b,?_⟩
    norm_num [eval,step,shiftPair] <;> push_cast <;> ring
  · refine ⟨1+a-2*b,-1-2*a+3*b,?_⟩
    norm_num [eval,step,shiftPair] <;> push_cast <;> ring
  · refine ⟨1+a-2*b,-2*a+3*b,?_⟩
    norm_num [eval,step,shiftPair] <;> push_cast <;> ring
  · refine ⟨2+a-2*b,-1-2*a+3*b,?_⟩
    norm_num [eval,step,shiftPair] <;> push_cast <;> ring

theorem finite_coordinates (alpha : ℕ → Label) (x : ℕ → ℝ)
    (omega : OperationOmega alpha x) (finite : OperationFiniteSource alpha) :
    ∀ p, IntegerCoordinate (x p) := by
  obtain ⟨M,tail⟩ := finite
  have zero := omega_tail_zero alpha x omega M tail
  have recurrence := omega.choose_spec.2.2.2
  have backward (n : ℕ) : ∀ p, p+n=M → IntegerCoordinate (x p) := by
    induction n with
    | zero =>
      intro p hp
      have hpM : M ≤ p := by omega
      rw [zero p hpM]
      exact integer_zero
    | succ n ih =>
      intro p hp
      rw [recurrence p]
      exact integer_branch _ (ih (p+1) (by omega))
  intro p
  by_cases hp : M ≤ p
  · rw [zero p hp]
    exact integer_zero
  · exact backward (M-p) p (by omega)

private theorem irrational_t : Irrational t := by
  convert Real.goldenConj_irrational.neg using 1
  dsimp [t,Real.goldenConj]
  ring

private theorem coefficient_unique (a b c d : ℚ)
    (he : (a : ℝ)+(b : ℝ)*t = (c : ℝ)+(d : ℝ)*t) : a=c ∧ b=d := by
  by_cases hb : b=d
  · subst d
    have ha : (a : ℝ) = (c : ℝ) := by linarith
    exact ⟨Rat.cast_injective ha,rfl⟩
  · exfalso
    apply irrational_t.ne_rat ((c-a)/(b-d))
    push_cast
    apply (eq_div_iff (by exact_mod_cast sub_ne_zero.mpr hb)).mpr
    linarith

/-- The four critical common-suffix contacts cannot be finite-source coordinates. -/
theorem contact_excluded (j : ℤ) (hlo : 1 ≤ j) (hhi : j ≤ 4) :
    ¬ IntegerCoordinate (-1+(j : ℝ)*phi/5) := by
  rintro ⟨a,b,he⟩
  have equation : ((j/5-1 : ℚ) : ℝ)+((j/5 : ℚ) : ℝ)*t =
      ((a : ℚ) : ℝ)+((b : ℚ) : ℝ)*t := by
    push_cast
    dsimp [phi] at he
    linarith
  have coefficients := coefficient_unique (j/5-1) (j/5) a b equation
  have real_eq : (j : ℝ)/5 = (b : ℝ) := by exact_mod_cast coefficients.2
  have int_eq : j = 5*b := by exact_mod_cast (show (j : ℝ)=5*(b : ℝ) by linarith)
  omega

#print axioms finite_coordinates
#print axioms contact_excluded
end
end Reg.Support.FibonacciFiniteCoordinates
