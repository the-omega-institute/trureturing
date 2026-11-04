import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Valuation5040.PrimeValuation5040Sigma
import Reg.Support.DependentFamily

/-! Source-bound registration for the restored strict 5040 threshold equivalence. -/

open _root_.D5.S3.Arith.Robin.Valuation5040.PrimeValuation5040Sigma
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.Valuation5040.PrimeValuation5040Sigma

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def anchorFn : ∀ (_ : signature.Anchor) p, signature.State p :=
  fun e => nomatch e

def actual : Realization signature :=
  realize signature (fun _ _ b => if b then False else
    ∀ {n : ℕ} (hn0 : n ≠ 0) (hn : n.Coprime 210),
      ((ArithmeticFunction.sigma 1 (5040 * n) : ℝ) / (5040 * n) > 2) ↔
        ((ArithmeticFunction.sigma 1 n : ℝ) / n > (210 / 403 : ℝ))) anchorFn

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) anchorFn

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () false

private theorem rejected_law : ¬ arena.Law rejected := by
  simp [arena, rejected, realize]

def registration : Registration arena (type_of% @normalized_sigma_5040_gt_two_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by simpa [arena, actual, realize] using @normalized_sigma_5040_gt_two_iff,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), false, true, ?_⟩
    change (∀ {n : ℕ} (hn0 : n ≠ 0) (hn : n.Coprime 210),
      ((ArithmeticFunction.sigma 1 (5040 * n) : ℝ) / (5040 * n) > 2) ↔
        ((ArithmeticFunction.sigma 1 n : ℝ) / n > (210 / 403 : ℝ))) ≠ False
    intro h
    have hp : (∀ {n : ℕ} (hn0 : n ≠ 0) (hn : n.Coprime 210),
      ((ArithmeticFunction.sigma 1 (5040 * n) : ℝ) / (5040 * n) > 2) ↔
        ((ArithmeticFunction.sigma 1 n : ℝ) / n > (210 / 403 : ℝ))) :=
      @normalized_sigma_5040_gt_two_iff
    exact h ▸ hp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@normalized_sigma_5040_gt_two_iff) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Valuation5040.PrimeValuation5040Sigma.normalized_sigma_5040_gt_two_iff.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Valuation5040.PrimeValuation5040Sigma.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => if b then False else
    ∀ {n : ℕ} (hn0 : n ≠ 0) (hn : n.Coprime 210),
      ((ArithmeticFunction.sigma 1 (5040 * n) : ℝ) / (5040 * n) > 2) ↔
        ((ArithmeticFunction.sigma 1 n : ℝ) / n > (210 / 403 : ℝ))) anchorFn)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end Reg.D5.S3.Arith.Robin.Valuation5040.PrimeValuation5040Sigma

