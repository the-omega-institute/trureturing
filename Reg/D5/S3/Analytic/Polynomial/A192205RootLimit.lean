import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Polynomial.A192205RootLimit
import Reg.Support.DependentFamily

/-! Source-bound audit of the complete original theorem. -/

namespace Reg.D5.S3.Analytic.Polynomial.A192205RootLimit
open _root_.D5.S3.Analytic.Polynomial.A192205RootLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter
open scoped Topology
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := Tendsto (fun n : ℕ => (r.readout () () n : ℝ) ^ (1/(n:ℝ)))
    atTop (𝓝 (16*Real.sqrt 3/9))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he : (1:ℝ) = 16*Real.sqrt 3/9 :=
    by simpa [arena, rejected, realize] using h
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  nlinarith
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, a, p, Finset.sum_range_succ, Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]
def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.unit
  realizationName := `Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Polynomial.A192205RootLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end
end Reg.D5.S3.Analytic.Polynomial.A192205RootLimit
