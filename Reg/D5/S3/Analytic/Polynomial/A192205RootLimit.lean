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

namespace Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.DegreeRoot
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
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 3*(n:ℝ)+1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := Tendsto (fun n : ℕ => (r.readout () () n) ^ (1/(n:ℝ))) atTop (𝓝 1)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Tendsto (fun n : ℕ => (rejected.readout () () n) ^ (1/(n:ℝ)))
      atTop (𝓝 (0:ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
    simp [rejected, realize, Real.zero_rpow (show (1/(n:ℝ)) ≠ 0 by positivity)]
  exact zero_ne_one (tendsto_nhds_unique hz h)
def family : Registration arena (type_of% degree_root_limit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨degree_root_limit, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@degree_root_limit) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.DegreeRoot.unit
  realizationName := `Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.DegreeRoot.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => 3*(n:ℝ)+1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Polynomial.A192205RootLimit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.DegreeRoot

namespace Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.PowerSum
open _root_.D5.S3.Analytic.Polynomial.A192205RootLimit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section
abbrev signature : Signature where
  Params := Σ _ : ℂ[X], ℝ × ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q i => ‖(q.1^q.2.2).coeff i‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : ℂ[X]) (M : ℝ),
    (∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) → ∀ (n : ℕ),
    (∑ i ∈ (p^n).support, r.readout () ⟨p, M, n⟩ i)^2 ≤
      ((p^n).support.card : ℝ) * M^(2*n)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hM : ∀ z : ℂ, ‖z‖ = 1 → ‖(1:ℂ[X]).eval z‖ ≤ (1:ℝ) := by
    intro z hz
    norm_num
  have hb := h (1:ℂ[X]) 1 hM 0
  norm_num [rejected, realize] at hb
def family : Registration arena (type_of% @power_sum_sq_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@power_sum_sq_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨(1:ℂ[X]), 1, 0⟩, 0, 1, ?_⟩
    norm_num [actual, realize]
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@power_sum_sq_le) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.PowerSum.unit
  realizationName := `Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.PowerSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q i => ‖(q.1^q.2.2).coeff i‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Polynomial.A192205RootLimit
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Analytic.Polynomial.A192205RootLimit.PowerSum
