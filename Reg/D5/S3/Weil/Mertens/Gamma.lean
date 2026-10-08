import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.Gamma
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Weil.Mertens.Gamma
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

-- The parameter telescope is empty; the state is the original integration variable.
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := (∫ t in Ioi (0 : ℝ), (R.readout () () t : ℝ)) = deriv Real.Gamma 1

def actual : Realization signature :=
  realize signature
    (fun (_ : Unit) (_ : Unit) (t : ℝ) => Real.log t * Real.exp (-t))
    (fun e => nomatch e)

-- Its integral is Γ'(1) + 1, so rejection needs no estimate for Γ'(1).
def rejected : Realization signature :=
  realize signature
    (fun (_ : Unit) (_ : Unit) (t : ℝ) => (deriv Real.Gamma 1 + 1) * Real.exp (-t))
    (fun e => nomatch e)

theorem rejected_integral :
    (∫ t in Ioi (0 : ℝ), (rejected.readout () () t : ℝ)) = deriv Real.Gamma 1 + 1 := by
  change (∫ t in Ioi (0 : ℝ), (deriv Real.Gamma 1 + 1) * Real.exp (-t)) = _
  rw [integral_const_mul]
  have h : (∫ t in Ioi (0 : ℝ), Real.exp (-t)) = 1 := by
    simpa using integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
  rw [h, mul_one]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (∫ t in Ioi (0 : ℝ), (rejected.readout () () t : ℝ)) = deriv Real.Gamma 1 at h
  rw [rejected_integral] at h
  linarith

def registration : Registration arena
    ((∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t)) = deriv Real.Gamma 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.integral_log_mul_exp_neg_eq_deriv_Gamma, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), Real.exp 1, ?_⟩
    change Real.log 1 * Real.exp (-1) ≠ Real.log (Real.exp 1) * Real.exp (-Real.exp 1)
    simp only [Real.log_one, zero_mul, Real.log_exp, one_mul]
    exact ne_of_lt (Real.exp_pos _)

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.integral_log_mul_exp_neg_eq_deriv_Gamma) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun (_ : Unit) (_ : Unit) (t : ℝ) => Real.log t * Real.exp (-t))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "integral_log_mul_exp_neg_eq_deriv_Gamma") "Reg.D5.S3.Weil.Mertens.Gamma/Reg.D5.S3.Weil.Mertens.Gamma.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Weil.Mertens.Gamma.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun (_ : Unit) (_ : Unit) (t : ℝ) => Real.log t * Real.exp (-t))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Weil.Mertens.Gamma, definition := none, coordinates := #[], readouts := #[{ path := #["fn", "arg", "arg", "body"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration
end
end Reg.D5.S3.Weil.Mertens.Gamma
