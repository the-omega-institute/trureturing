import Reg.Support.FibonacciFiniteSource
import Mathlib.Tactic.FinCases

namespace Reg.Support.FibonacciBranchSeparation
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
noncomputable section

def lower : Label → ℝ
  | .L3 => -1
  | .L0 => -T2
  | .L5 => g
  | .L2 => t
  | .L25 => 2*t

def upper : Label → ℝ
  | .L3 => -T2
  | .L0 => g
  | .L5 => t
  | .L2 => 2*t
  | .L25 => phi

private theorem supported_range (s e : Guard) (l : Label) (z : ℝ)
    (edge : nextGuard s l = some e) (support : InSupport e z) :
    lower l ≤ branch l z ∧ branch l z ≤ upper l := by
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  have prodLo := mul_le_mul_of_nonneg_left support.1 hgpositive.le
  have prodHi := mul_le_mul_of_nonneg_left support.2 hgpositive.le
  cases s <;> cases l <;> cases e <;> simp only [nextGuard,reduceCtorEq] at edge
  all_goals try contradiction
  all_goals norm_num [lower,upper,InSupport,supportUpper,branch,shift,phi,T2,g]
    at prodLo prodHi ⊢
  all_goals constructor <;> nlinarith [ht]

/-- Actual legal guarded branches have these five closed image ranges. -/
theorem omega_branch_range (alpha : ℕ → Label) (x : ℕ → ℝ)
    (omega : OperationOmega alpha x) (p : ℕ) :
    lower (alpha p) ≤ x p ∧ x p ≤ upper (alpha p) := by
  obtain ⟨path,h0,edges,support,recurrence⟩ := omega
  rw [recurrence p]
  exact supported_range _ _ _ _ (edges p) (support (p+1))

private theorem color_0 (theta : ℝ) (htheta : theta < lam)
    (l m : Label) (z : ℝ)
    (lx : lower l ≤ branch l z ∧ branch l z ≤ upper l)
    (mx : lower m ≤ branch m z ∧ branch m z ≤ upper m)
    (lc : ClosedExpanded theta (0 : Color) (branch l z))
    (mc : ClosedExpanded theta (0 : Color) (branch m z)) : l=m := by
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  cases l <;> cases m <;> try rfl
  all_goals norm_num [lower,upper,ClosedExpanded,branch,shift,cut,lam,T2,phi,g] at *
  all_goals nlinarith [ht]

private theorem color_1 (theta : ℝ) (htheta : theta < lam)
    (l m : Label) (z : ℝ)
    (lx : lower l ≤ branch l z ∧ branch l z ≤ upper l)
    (mx : lower m ≤ branch m z ∧ branch m z ≤ upper m)
    (lc : ClosedExpanded theta (1 : Color) (branch l z))
    (mc : ClosedExpanded theta (1 : Color) (branch m z)) : l=m := by
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  cases l <;> cases m <;> try rfl
  all_goals norm_num [lower,upper,ClosedExpanded,branch,shift,cut,lam,T2,phi,g] at *
  all_goals nlinarith [ht]

private theorem color_2 (theta : ℝ) (htheta : theta < lam)
    (l m : Label) (z : ℝ)
    (lx : lower l ≤ branch l z ∧ branch l z ≤ upper l)
    (mx : lower m ≤ branch m z ∧ branch m z ≤ upper m)
    (lc : ClosedExpanded theta (2 : Color) (branch l z))
    (mc : ClosedExpanded theta (2 : Color) (branch m z)) : l=m := by
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  cases l <;> cases m <;> try rfl
  all_goals norm_num [lower,upper,ClosedExpanded,branch,shift,cut,lam,T2,phi,g] at *
  all_goals nlinarith [ht]

private theorem color_3 (theta : ℝ) (htheta : theta < lam)
    (l m : Label) (z : ℝ)
    (lx : lower l ≤ branch l z ∧ branch l z ≤ upper l)
    (mx : lower m ≤ branch m z ∧ branch m z ≤ upper m)
    (lc : ClosedExpanded theta (3 : Color) (branch l z))
    (mc : ClosedExpanded theta (3 : Color) (branch m z)) : l=m := by
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  cases l <;> cases m <;> try rfl
  all_goals norm_num [lower,upper,ClosedExpanded,branch,shift,cut,lam,T2,phi,g] at *
  all_goals nlinarith [ht]

private theorem color_4 (theta : ℝ) (htheta : theta < lam)
    (l m : Label) (z : ℝ)
    (lx : lower l ≤ branch l z ∧ branch l z ≤ upper l)
    (mx : lower m ≤ branch m z ∧ branch m z ≤ upper m)
    (lc : ClosedExpanded theta (4 : Color) (branch l z))
    (mc : ClosedExpanded theta (4 : Color) (branch m z)) : l=m := by
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  cases l <;> cases m <;> try rfl
  all_goals norm_num [lower,upper,ClosedExpanded,branch,shift,cut,lam,T2,phi,g] at *
  all_goals nlinarith [ht]

private theorem color_5 (theta : ℝ) (htheta : theta < lam)
    (l m : Label) (z : ℝ)
    (lx : lower l ≤ branch l z ∧ branch l z ≤ upper l)
    (mx : lower m ≤ branch m z ∧ branch m z ≤ upper m)
    (lc : ClosedExpanded theta (5 : Color) (branch l z))
    (mc : ClosedExpanded theta (5 : Color) (branch m z)) : l=m := by
  rcases tail_arithmetic with ⟨ht,hpositive,htone,hgpositive,hgone,hphi⟩
  cases l <;> cases m <;> try rfl
  all_goals norm_num [lower,upper,ClosedExpanded,branch,shift,cut,lam,T2,phi,g] at *
  all_goals nlinarith [ht]

/-- Below lam, a common suffix and the same closed observation determine the current label. -/
theorem same_suffix_label (theta : ℝ) (htheta : theta < lam)
    (l m : Label) (z : ℝ) (c : Color)
    (lx : lower l ≤ branch l z ∧ branch l z ≤ upper l)
    (mx : lower m ≤ branch m z ∧ branch m z ≤ upper m)
    (lc : ClosedExpanded theta c (branch l z))
    (mc : ClosedExpanded theta c (branch m z)) : l=m := by
  fin_cases c
  · exact color_0 theta htheta l m z lx mx lc mc
  · exact color_1 theta htheta l m z lx mx lc mc
  · exact color_2 theta htheta l m z lx mx lc mc
  · exact color_3 theta htheta l m z lx mx lc mc
  · exact color_4 theta htheta l m z lx mx lc mc
  · exact color_5 theta htheta l m z lx mx lc mc

/-- Full closed observation agreement identifies finite sources below lam.
This full-record uniqueness statement does not assert finite-prefix isolation. -/
theorem finite_compatible_unique_below (theta : ℝ) (htheta : theta < lam)
    (alpha beta : ℕ → Label) (x y : ℕ → ℝ)
    (ox : OperationOmega alpha x) (oy : OperationOmega beta y)
    (fx : OperationFiniteSource alpha) (fy : OperationFiniteSource beta)
    (r : ℕ → Color)
    (cx : ∀ p, ClosedExpanded theta (r p) (x p))
    (cy : ∀ p, ClosedExpanded theta (r p) (y p)) : alpha=beta := by
  obtain ⟨Mx,tx⟩ := fx
  obtain ⟨My,ty⟩ := fy
  let M := max Mx My
  have zx := Reg.Support.FibonacciFiniteSource.omega_tail_zero alpha x ox Mx tx
  have zy := Reg.Support.FibonacciFiniteSource.omega_tail_zero beta y oy My ty
  have backward (n : ℕ) : ∀ p, p+n=M → alpha p=beta p ∧ x p=y p := by
    induction n with
    | zero =>
      intro p hp
      have hxp : Mx ≤ p := by dsimp [M] at hp; omega
      have hyp : My ≤ p := by dsimp [M] at hp; omega
      exact ⟨(tx p hxp).trans (ty p hyp).symm,(zx p hxp).trans (zy p hyp).symm⟩
    | succ n ih =>
      intro p hp
      have next := ih (p+1) (by omega)
      have vx := ox.choose_spec.2.2.2 p
      have vy := oy.choose_spec.2.2.2 p
      have rx := omega_branch_range alpha x ox p
      have ry := omega_branch_range beta y oy p
      have ex := cx p
      have ey := cy p
      rw [vx] at rx ex
      rw [vy,← next.2] at ry ey
      have labels := same_suffix_label theta htheta (alpha p) (beta p) (x (p+1))
        (r p) rx ry ex ey
      refine ⟨labels,?_⟩
      rw [vx,vy,labels,next.2]
  funext p
  by_cases hp : M ≤ p
  · have hxp : Mx ≤ p := (le_max_left _ _).trans hp
    have hyp : My ≤ p := (le_max_right _ _).trans hp
    exact (tx p hxp).trans (ty p hyp).symm
  · exact (backward (M-p) p (by omega)).1

#print axioms omega_branch_range
#print axioms same_suffix_label
#print axioms finite_compatible_unique_below
end
end Reg.Support.FibonacciBranchSeparation
