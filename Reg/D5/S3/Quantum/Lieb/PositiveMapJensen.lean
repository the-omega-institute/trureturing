/- Source candidates only. Current kernel, source reconstruction, enrollment
and binding checks are pending; no registration is asserted validated. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Lieb.PositiveMapJensen
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Lieb.PositiveMapJensen
open LownerHeinzTheorem JensenOperatorInequality LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
universe u v

namespace Reg.D5.S3.Quantum.Lieb.PositiveMapJensen

namespace FunctionObservation

/-- The selected source data is f itself at a single CFC/perspective occurrence.
All hypotheses and every other occurrence of f remain fixed in each law. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ f x => f x + 1) (fun e => nomatch e)

theorem zero_convex :
    OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) (fun _ => 0) := by
  intro K _ _ _ _ A B t hA hB ht0 ht1 hAs hBs
  simp [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  exact zero_ne_one (congrFun h 0)

theorem not_one_le_zero {n : Type u} [Fintype n] [DecidableEq n]
    [Nonempty n] : ¬ (1 : Matrix n n ℂ) ≤ 0 := by
  intro h
  exact one_ne_zero (le_antisymm h Matrix.PosSemidef.one.nonneg)

end FunctionObservation

namespace Intertwining
open FunctionObservation

def arena : Arena where
  signature := signature
  Law r := ∀ {n : Type u} {m : Type v}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (V : Matrix n m ℂ)
    (hAV : A * V = V * B) (f : ℝ → ℝ),
    cfc (r.readout () () f) A * V = V * cfc f B

private theorem actual_law : arena.{u,v}.Law actual := by
  exact @cfc_intertwining.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro hall
  let n := ULift.{u} (Fin 1)
  let m := ULift.{v} (Fin 1)
  let V : Matrix n m ℂ := fun _ _ => 1
  have h := hall (0 : Matrix n n ℂ) (0 : Matrix m m ℂ)
    (by simp) (by simp) V (by simp) (fun _ => 0)
  have hz : V = 0 := by simpa [rejected, realize] using h
  exact one_ne_zero (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def family : Registration arena.{u,v} (type_of% (@cfc_intertwining.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (by cases j; cases i; rfl)).elim
    · intro e
      exact nomatch e
  dependence := dependence

/-- Source occurrence coordinates are authored candidates, pending extraction. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cfc_intertwining.{u,v}) (Realization FunctionObservation.signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Lieb.PositiveMapJensen.Intertwining.unit
  realizationName := `Reg.D5.S3.Quantum.Lieb.PositiveMapJensen.Intertwining.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize FunctionObservation.signature
    FunctionObservation.actual.readout FunctionObservation.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Lieb.PositiveMapJensen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Intertwining

namespace Jensen
open FunctionObservation

def arena : Arena where
  signature := signature
  Law r := ∀ {n m : Type u}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {f : ℝ → ℝ}
    (hconv : OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) (hΦ : Φ 1 = 1)
    (A : Matrix n n ℂ) (hA : A.PosSemidef),
    cfc (r.readout () () f) (Φ A) ≤ Φ (cfc f A)

private theorem actual_law : arena.{u}.Law actual := by
  exact @positive_unital_jensen.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hall
  let n := ULift.{u} (Fin 1)
  have h := hall (f := fun _ => 0) (@zero_convex.{u}) continuousOn_const
    (PositiveLinearMap.id ℂ (Matrix n n ℂ)) rfl 0 Matrix.PosSemidef.zero
  apply not_one_le_zero (n := n)
  simpa [rejected, realize] using h

def family : Registration arena.{u} (type_of% (@positive_unital_jensen.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (by cases j; cases i; rfl)).elim
    · intro e
      exact nomatch e
  dependence := dependence

/-- Source occurrence coordinates are authored candidates, pending extraction. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_unital_jensen.{u}) (Realization FunctionObservation.signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Lieb.PositiveMapJensen.Jensen.unit
  realizationName := `Reg.D5.S3.Quantum.Lieb.PositiveMapJensen.Jensen.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize FunctionObservation.signature
    FunctionObservation.actual.readout FunctionObservation.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Lieb.PositiveMapJensen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Jensen

namespace Congruence

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := Matrix p.1 p.2 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.2 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {n : Type u} {m : Type v}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {A B : Matrix n n ℂ} (hAB : A ≤ B) (V : Matrix n m ℂ),
    Vᴴ * A * V ≤ Vᴴ * B * r.readout () ⟨n,m⟩ V

private theorem actual_law : arena.{u,v}.Law actual := by
  exact @congruence_mono.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro hall
  let n := ULift.{u} (Fin 1)
  let m := ULift.{v} (Fin 1)
  let V : Matrix n m ℂ := fun _ _ => 1
  have h := hall (A := (1 : Matrix n n ℂ)) (B := 1) le_rfl V
  have hGram : Vᴴ * V = (1 : Matrix m m ℂ) := by
    ext i j
    change (∑ k : n, star (V k i) * V k j) = if i = j then 1 else 0
    simp [V, n, m, Subsingleton.elim i j]
  apply FunctionObservation.not_one_le_zero (n := m)
  simpa [rejected, realize, hGram] using h

def family : Registration arena.{u,v} (type_of% (@congruence_mono.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (by cases j; cases i; rfl)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩,
      (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

/-- The raw source selector and every proof here await current checks. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@congruence_mono.{u,v}) (Realization signature.{u,v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Lieb.PositiveMapJensen.Congruence.unit
  realizationName := `Reg.D5.S3.Quantum.Lieb.PositiveMapJensen.Congruence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Lieb.PositiveMapJensen
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Congruence

end Reg.D5.S3.Quantum.Lieb.PositiveMapJensen
