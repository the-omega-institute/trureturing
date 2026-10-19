/- Source candidates only. Current kernel, source reconstruction, enrollment
and binding checks are pending; no registration is asserted validated. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Lieb.SupportPerspectiveTransport
import Reg.D5.S3.Quantum.Lieb.PositiveMapJensen

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Lieb.PositiveMapJensen
open LownerHeinzTheorem JensenOperatorInequality LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
universe u v

open _root_.D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open Reg.D5.S3.Quantum.Lieb.PositiveMapJensen

namespace Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport

namespace Localization
open FunctionObservation

def arena : Arena where
  signature := signature
  Law r := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (P Y R : Matrix n n ℂ)
    (hP : Pᴴ = P) (hPP : P * P = P) (hY : Y.IsHermitian)
    (hPY : P * Y = Y) (hPR : P * R = R) (hRP : R * P = R)
    (t : ℝ) (f : ℝ → ℝ),
    R * cfc (r.readout () () f) (Y + t • (1 - P)) * R = R * cfc f Y * R

private theorem actual_law : arena.{u}.Law actual := by
  exact @cfc_supported_localization.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hall
  let n := ULift.{u} (Fin 1)
  have h := hall (1 : Matrix n n ℂ) 0 1 (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) 0 (fun _ => 0)
  have hz : (1 : Matrix n n ℂ) = 0 := by simpa [rejected, realize] using h
  exact one_ne_zero hz

def family : Registration arena.{u} (type_of% (@cfc_supported_localization.{u})) where
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
    (@cfc_supported_localization.{u}) (Realization FunctionObservation.signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport.Localization.unit
  realizationName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport.Localization.family
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
    owner := `D5.S3.Quantum.Lieb.SupportPerspectiveTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Localization

namespace AmbientJensen
open FunctionObservation

def arena : Arena where
  signature := signature
  Law r := ∀ {a b : Type u}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {f : ℝ → ℝ}
    (hconv : OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (Φ : Matrix a a ℂ →ₚ[ℂ] Matrix b b ℂ)
    (B : Matrix a a ℂ) (hB : B.PosSemidef) (i : a)
    (X : Matrix a a ℂ) (hX : X.PosSemidef),
    cfc (r.readout () () f) (normalizedPositiveMap Φ B X +
        X i i • (1 - spectralSupport (Φ B))) ≤
      normalizedPositiveMap Φ B (cfc f X) +
        (cfc f X) i i • (1 - spectralSupport (Φ B))

private theorem actual_law : arena.{u}.Law actual := by
  exact @ambient_unitalized_jensen.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hall
  let n := ULift.{u} (Fin 1)
  have h := hall (f := fun _ => 0) (@zero_convex.{u}) continuousOn_const
    (PositiveLinearMap.id ℂ (Matrix n n ℂ)) 1 Matrix.PosSemidef.one
    (ULift.up 0) 0 Matrix.PosSemidef.zero
  apply not_one_le_zero (n := n)
  simpa [rejected, realize, normalizedPositiveMap] using h

def family : Registration arena.{u} (type_of% (@ambient_unitalized_jensen.{u})) where
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
    (@ambient_unitalized_jensen.{u}) (Realization FunctionObservation.signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport.AmbientJensen.unit
  realizationName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport.AmbientJensen.family
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
    owner := `D5.S3.Quantum.Lieb.SupportPerspectiveTransport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end AmbientJensen

namespace Normalization

abbrev signature : Signature where
  Params := Type u
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law r := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℂ) (hQ : Q.PosSemidef),
    let R := CFC.sqrt Q
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    Rᴴ = R ∧ Wᴴ = W ∧ Pᴴ = P ∧ P * P = P ∧
      P * R = R ∧ R * P = R ∧ P * Q = r.readout () n Q ∧ W * Q * W = P

private theorem actual_law : arena.{u}.Law actual := by
  exact @spectral_sqrt_normalization.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hall
  let n := ULift.{u} (Fin 1)
  have h := hall (0 : Matrix n n ℂ) Matrix.PosSemidef.zero
  have hz : (0 : Matrix n n ℂ) = (fun _ _ => 1) := by
    simpa [rejected, realize] using h.2.2.2.2.2.2.1
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def family : Registration arena.{u} (type_of% (@spectral_sqrt_normalization.{u})) where
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
    refine ⟨ULift.{u} (Fin 1), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

/-- The raw source selector and every proof here await current checks. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@spectral_sqrt_normalization.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport.Normalization.unit
  realizationName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport.Normalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Lieb.SupportPerspectiveTransport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Normalization

/- The signed-support law below retains the complete original telescope.
Its actual law is definitionally the original statement. The selected RHS S
is a local let; a faithful raw source selector is still pending. -/

namespace SignedSupport

abbrev signature : Signature where
  Params := Type v
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{v}
  Law r := ∀ {n : Type u} {m : Type v}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ)
    (B : Matrix n n ℂ) (hB : B.PosSemidef)
    (Z : Matrix n n ℂ) (hZ : Z.IsHermitian),
    let S := Φ (CFC.sqrt B * Z * CFC.sqrt B)
    let P := spectralSupport (Φ B)
    P * S = r.readout () m S ∧ S * P = S

private theorem actual_law : arena.{u,v}.Law actual := by
  exact @positive_map_sandwich_support.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro hall
  let n := ULift.{u} (Fin 1)
  let m := ULift.{v} (Fin 1)
  have h := hall (0 : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ)
    0 Matrix.PosSemidef.zero 0 (by simp)
  have hz : (0 : Matrix m m ℂ) = (fun _ _ => 1) := by
    simpa [rejected, realize] using h.1
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def family : Registration arena.{u,v} (type_of% (@positive_map_sandwich_support.{u,v})) where
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
    refine ⟨ULift.{v} (Fin 1), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

/-- The raw source selector and every proof here await current checks. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_map_sandwich_support.{u,v}) (Realization signature.{v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport.SignedSupport.unit
  realizationName := `Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport.SignedSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end SignedSupport

end Reg.D5.S3.Quantum.Lieb.SupportPerspectiveTransport
