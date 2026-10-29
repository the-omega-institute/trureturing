import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Hiai.CommonLowerHarmonicBound

noncomputable section
namespace Reg.D5.S3.Quantum.Hiai.CommonLowerHarmonicBound
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Hiai.ParallelSumVariational
open _root_.D5.S3.Quantum.Hiai.CommonLowerHarmonicBound
open scoped MatrixOrder ComplexOrder

abbrev signature.{u} : Signature where
  Params := Σ n : Type u, Fintype n × DecidableEq n
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u} : Realization signature.{u} :=
  realize signature (fun _ p X => by
    letI := p.2.1
    letI := p.2.2
    exact fun Y => X ≤ Y) (fun e => nomatch e)

def bad.{u} : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena.{u} : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [hn : Fintype n] [hd : DecidableEq n]
    {P Q K : Matrix n n ℂ}, K.PosSemidef → K ≤ P → K ≤ Q →
    ∀ W : Matrix n n ℂ × Matrix n n ℂ, W.1 + W.2 = 1 →
      R.readout () ⟨n, hn, hd⟩ K ((2 : ℝ) • splitEnergy P Q W)

private theorem bad_law.{u} : ¬ arena.{u}.Law bad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance 0 0 0
    Matrix.PosSemidef.zero le_rfl le_rfl (1, 0) (by simp)

private theorem dependence.{u} : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, inferInstance⟩, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) ≤ 0) = (1 ≤ 0) at he
  have hh : (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) ≤ 0 := Eq.mp he le_rfl
  have ht := (Matrix.le_iff.mp hh).trace_nonneg
  norm_num [Matrix.trace] at ht

def family.{u} : Registration arena.{u} (type_of% (@common_lower_split_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@common_lower_split_bound.{u}, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨bad, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, bad_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration.{u} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@common_lower_split_bound.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.CommonLowerHarmonicBound.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.CommonLowerHarmonicBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p X => by
    letI := p.2.1
    letI := p.2.2
    exact fun Y => X ≤ Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.CommonLowerHarmonicBound
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.Quantum.Hiai.CommonLowerHarmonicBound
