import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntrySlowTail
import Reg.Support.SingleDependentReadout

/-! # Source-bound audit of the conditional analytic tail transfer -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter

namespace Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail
open _root_.D5.S3.StatisticalMechanics.SingleEntrySlowTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actualReadout : ∀ role p, signature.State p → signature.Output role p := fun _ _ x => x

def actualAnchor : ∀ (_ : signature.Anchor) p, signature.State p := fun e => nomatch e

def actual : Realization signature := realize signature actualReadout actualAnchor

def rejected : Realization signature := realize signature (fun _ _ _ => 0) actualAnchor

/-- The original functions, all differential and asymptotic hypotheses, and the
limit value are retained. Only the slope occurrence in the positivity conclusion
is observed, so changing it cannot alter any premise. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D f K : ℝ → ℝ) (s l theta rInf qi qj slope : ℝ),
    l < s → 0 < theta → 0 < rInf → 0 < qi → 0 < qj → slope < 0 →
    (∀ t, 0 ≤ t → HasDerivAt D (-s * D t + f t * K t) t) →
    Tendsto (fun t => Real.exp (l * t) * f t) atTop (nhds (-theta / slope)) →
    Tendsto K atTop (nhds (rInf * qi * qj)) →
    Tendsto (fun t => Real.exp (l * t) * D t) atTop
      (nhds (-theta * rInf * qi * qj / ((s - l) * slope))) ∧
      0 < -theta * rInf * qi * qj / ((s - l) * R.readout () () slope)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun _ : ℝ => (1 : ℝ))
      (-(1 : ℝ) * 1 + 1 * 1) t := by
    intro t _
    simpa using hasDerivAt_const t (1 : ℝ)
  have hf : Tendsto (fun t : ℝ => Real.exp ((0 : ℝ) * t) * 1)
      atTop (nhds (-(1 : ℝ) / -1)) := by simpa using tendsto_const_nhds
  have hK : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds ((1 : ℝ) * 1 * 1)) :=
    by simpa using tendsto_const_nhds
  have hh := (h (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 0 1 1 1 1 (-1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hd hf hK).2
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, actualReadout, realize]

def family : Registration arena (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨association_tail_from_input_tail, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySlowTail
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body", "body", "body", "body",
      "arg", "arg", "arg", "arg"]
    stateBinder := 9
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``association_tail_from_input_tail).type
  let path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "body", "body", "body", "body", "body",
    "arg", "arg", "arg", "arg"]
  let mut binders := 0
  for step in path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected slow-tail slope occurrence is absent"
  unless binders == 19 && e == .bvar 9 do
    throwError "The selected occurrence is not the original real slope parameter"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    association_tail_from_input_tail (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

def analysisSource : Analysis.Source association_tail_from_input_tail :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application association_tail_from_input_tail where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Conditional analytic functions: generator-bound probability law, pair pushforward and spectral input residue are not premises of this source" }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis

end Reg.D5.S3.StatisticalMechanics.SingleEntrySlowTail
