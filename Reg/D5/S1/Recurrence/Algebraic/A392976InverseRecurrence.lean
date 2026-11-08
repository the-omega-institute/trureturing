import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.A392976InverseRecurrence
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S1.Recurrence.Algebraic.A392976InverseRecurrence
open _root_.D5.S1.Recurrence.Algebraic.A392976InverseRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open PowerSeries

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ n => if n = 5 then 1 else 0) (fun e => nomatch e)

/-- The inverse, quotient, D-finiteness and every recurrence index are retained. -/
def arena : Arena where
  signature := signature
  Law R :=
  constantCoeff U = 0 ∧
  (f : PowerSeries ℚ).subst U = X ∧
  U.subst (f : PowerSeries ℚ) = X ∧
  (∀ V : PowerSeries ℚ, constantCoeff V = 0 →
    (f : PowerSeries ℚ).subst V = X → V = U) ∧
  X * A = U ∧ DFinite A ∧ ∀ n : ℕ, 5 ≤ n →
    283*(n : ℚ)*(n-1)*(n-2)*(83022305213*n-178385058984)*(n+1)*R.readout () () n -
    6*n*(n-1)*(n-2)*(12196786904129*n^2-45110300936020*n+52641391340361)*R.readout () () (n-1) -
    6*(n-1)*(n-2)*(67790996421377*n^3-248299346995054*n^2+202497447227007*n+3061418504418)*R.readout () () (n-2) -
    2*(n-2)*(192167357944360*n^4-559010679688491*n^3-2120668219560541*n^2+9123363136130610*n-8342981628089220)*R.readout () () (n-3) +
    5*(15640122296875*n^5-565964885220500*n^4+4989857715427325*n^3-18667678380008380*n^2+32085126156301848*n-20925325629575136)*R.readout () () (n-4) +
    10*(5*n-17)*(5*n-18)*(5*n-21)*(5*n-19)*(22509687685*n-60308240636)*R.readout () () (n-5) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.2.2.2.2.2.2 5 (by decide)
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    have ha : a 0 = 1 := by
      norm_num [a, U, PowerSeries.coeff_one_substInvOfIsUnit,
        ← Units.val_inv_eq_inv_val, IsUnit.unit_spec, f, Polynomial.coeff_mul]
    have hex : ∃ n : ℕ, a 0 ≠ a n := by
      by_contra h
      push_neg at h
      have he (n : ℕ) : a n = 1 := (h n).symm.trans ha
      have hr := result.2.2.2.2.2.2 5 (by decide)
      norm_num [he] at hr
    obtain ⟨n, hn⟩ := hex
    exact ⟨(), 0, n, hn⟩

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    result (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Algebraic.A392976InverseRecurrence.result "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.A392976InverseRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.A392976InverseRecurrence
    definition := some `D5.S1.Recurrence.Algebraic.A392976InverseRecurrence.claim
    coordinates := #[]
    readouts := #[
      { path := #["arg", "arg", "arg", "arg", "arg", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg", "arg", "arg", "arg", "arg", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg", "arg", "arg", "arg", "arg", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg", "arg", "arg", "arg", "arg", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg", "arg", "arg", "arg", "arg", "arg", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["arg", "arg", "arg", "arg", "arg", "arg", "body", "body", "fn", "arg", "arg", "arg"]
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }
    ] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Recurrence.Algebraic.A392976InverseRecurrence
