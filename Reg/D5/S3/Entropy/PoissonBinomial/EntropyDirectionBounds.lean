import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds
open LeanInformationAudit
open scoped BigOperators

namespace Reg.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds
noncomputable section
set_option autoImplicit false

namespace log_divided_difference_lower
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ A B => (Real.log A - Real.log B)/(A-B)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A B : ℝ} (hB : 0 < B) (hBA : B < A) (hA : A < 1),
    -Real.log (A*B)/(1-A*B) ≤ R.readout () A B
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (A := 1/2) (B := 1/4) (by norm_num) (by norm_num) (by norm_num)
  have hl : 0 < -Real.log ((1/2:ℝ)*(1/4)) / (1-(1/2:ℝ)*(1/4)) :=
    div_pos (neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))) (by norm_num)
  exact (not_le_of_gt hl) hh

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.log_divided_difference_lower)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.log_divided_difference_lower, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    have hl : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    norm_num [actual,realize] at ⊢
    exact hl.symm

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.log_divided_difference_lower) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.log_divided_difference_lower.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.log_divided_difference_lower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ A B => (Real.log A - Real.log B)/(A-B)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end log_divided_difference_lower

namespace neg_log_product_lt_div
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ A B => -Real.log (A*B)/(1-A*B)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A B : ℝ} (hB : 0 < B) (hBA : B < A) (hA : A < 1),
    -Real.log (A*B) < R.readout () A B
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (A := 1/2) (B := 1/4) (by norm_num) (by norm_num) (by norm_num)
  have hl : 0 < -Real.log ((1/2:ℝ)*(1/4)) :=
    neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  exact (not_lt_of_ge hl.le) hh

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.neg_log_product_lt_div)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.neg_log_product_lt_div, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 2, ?_⟩
    have hl : Real.log (2:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    norm_num [actual,realize] at ⊢
    exact hl.symm

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.neg_log_product_lt_div) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.neg_log_product_lt_div.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.neg_log_product_lt_div.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ A B => -Real.log (A*B)/(1-A*B)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end neg_log_product_lt_div

namespace three_point_entropy_direction_bound
abbrev signature := Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ v0 v2 => -Real.log (v0*v2)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1:ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (hs : ∑ j, r j = 1)
    (v0 v1 v2 : ℝ) (h0 : 0 < v0) (h1 : 0 < v1) (h2 : 0 < v2)
    (hv : v0+v1+v2=1),
    let Q := threePointMass r v0 v1 v2 0
    let d := ∑ j, r j * (2*Real.log (Q ((j.castAdd 1).succ)) -
      Real.log (Q (j.castAdd 2)) - Real.log (Q j.succ.succ))
    HasDerivAt (fun t => ∑ k, Real.negMulLog (threePointMass r v0 v1 v2 t k)) d 0 ∧
      d ≤ R.readout () v0 v2
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (n := 1) (fun _ => 1) (by intro j; norm_num) (by simp)
    (1/3) (1/3) (1/3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  simp only [threePointMass, Fin.sum_univ_one] at hh
  norm_num [rejected, realize] at hh
  linarith only [hh]

def family : Registration arena (type_of% (@_root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.three_point_entropy_direction_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.three_point_entropy_direction_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    simpa [actual,realize] using neg_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2))) |>.symm

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.three_point_entropy_direction_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.three_point_entropy_direction_bound.__information_unit
  realizationName := `Reg.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds.three_point_entropy_direction_bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ v0 v2 => -Real.log (v0*v2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end three_point_entropy_direction_bound
end
end Reg.D5.S3.Entropy.PoissonBinomial.EntropyDirectionBounds
