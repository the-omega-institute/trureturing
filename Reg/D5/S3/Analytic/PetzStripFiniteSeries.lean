import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PetzStripFiniteSeries
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts of the finite overlap derivative and its boundary integral. -/

noncomputable section

open PetzStripFiniteSeries PetzCothStripMode PetzExponentialBoundaryEvaluation
open MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.Analytic.PetzStripFiniteSeries

universe u

namespace Derivative

abbrev signature : Signature where
  Params := Σ ι : Type u, Σ _ : Fintype ι, ι → ℝ
  State p := p.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ ⟨ι, inst, ω⟩ c => ∑ i : ι, c i * (ω i : ℂ))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [inst : Fintype ι] (ω : ι → ℝ) (c : ι → ℂ),
    HasDerivAt (finiteOverlap ω c) (R.readout () ⟨ι, inst, ω⟩ c) 0

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  let ω : ULift.{u} Unit → ℝ := fun _ => 1
  let c : ULift.{u} Unit → ℂ := fun _ => 1
  have h := (hasDerivAt_finiteOverlap_zero ω c).unique (law ω c)
  simpa [ω, c, rejected, realize] using h

def family : Registration arena.{u} (type_of% @hasDerivAt_finiteOverlap_zero.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_finiteOverlap_zero.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw.{u}⟩
      intro other h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    cases role
    refine ⟨⟨ULift.{u} Unit, inferInstance, fun _ => 1⟩, fun _ => 0, fun _ => 1, ?_⟩
    simp [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_finiteOverlap_zero.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `PetzStripFiniteSeries.hasDerivAt_finiteOverlap_zero.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzStripFiniteSeries.Derivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ ⟨ι, inst, ω⟩ c => ∑ i : ι, c i * (ω i : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzStripFiniteSeries
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Derivative

namespace Integral

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] (ω : ι → ℝ) (c : ι → ℂ)
    (_hc : (finiteOverlap ω c 0).re = 1)
    (_hL : ∀ s, 0 ≤ overlapDeficit ω c 0 s),
    Integrable (fun s => lowerWeight s * overlapDeficit ω c 0 s) ∧
      Integrable (fun s => petzWeight s * overlapDeficit ω c (1 / 2) s) ∧
      R.readout () ()
        ((∫ s, lowerWeight s * overlapDeficit ω c 0 s) +
          ∫ s, petzWeight s * overlapDeficit ω c (1 / 2) s)
        (-(deriv (finiteOverlap ω c) 0).re)

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  exact (law (ι := ULift.{u} Unit) (fun _ => 0) (fun _ => 1)
    (by simp [finiteOverlap])
    (by simp [overlapDeficit, finiteOverlap])).2.2

def family : Registration arena.{u} (type_of% @integral_finiteOverlap_strip.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_finiteOverlap_strip.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_finiteOverlap_strip.{u}) (Realization signature) Unit Unit where
  unitName := `PetzStripFiniteSeries.integral_finiteOverlap_strip.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzStripFiniteSeries.Integral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzStripFiniteSeries
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Integral

end Reg.D5.S3.Analytic.PetzStripFiniteSeries
