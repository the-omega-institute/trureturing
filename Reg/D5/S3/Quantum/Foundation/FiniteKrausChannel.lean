import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Foundation.FiniteKrausChannel

open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

structure Parameters.{u, v, w, z} where
  A : Type u
  B : Type v
  S : Type w
  κ : Type z
  instA : Fintype A
  decA : DecidableEq A
  instB : Fintype B
  instS : CommSemiring S
  starS : Star S
  instκ : Fintype κ
  M : κ → Matrix B A S
  N : κ → Matrix B A S

def tpCondition.{u, v, w, z} (p : Parameters.{u, v, w, z}) : Prop :=
  letI := p.instκ
  ∑ k, (p.N k).conjTranspose * (p.M k) = 1

def traceLaw.{u, v, w, z} (p : Parameters.{u, v, w, z})
    (x : Matrix p.A p.A p.S) : Prop :=
  letI := p.instA
  letI := p.decA
  letI := p.instB
  letI := p.instS
  letI := p.starS
  letI := p.instκ
  Matrix.trace (MatrixMap.of_kraus p.M p.N x) = Matrix.trace x

abbrev signature.{u, v, w, z} : Signature where
  Params := Parameters.{u, v, w, z}
  State p := Matrix p.A p.A p.S
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u, v, w, z} : Realization signature.{u, v, w, z} :=
  realize signature (fun _ p x => traceLaw p x) (fun e => nomatch e)

def rejected.{u, v, w, z} : Realization signature.{u, v, w, z} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena.{u, v, w, z} : Arena where
  signature := signature.{u, v, w, z}
  Law R := ∀ p : Parameters.{u, v, w, z}, tpCondition p →
    ∀ x, R.readout () p x

theorem rejected_law.{u, v, w, z} : ¬ arena.{u, v, w, z}.Law rejected := by
  intro h
  let p : Parameters.{u, v, w, z} := {
    A := ULift.{u} Unit, B := ULift.{v} Unit, S := ℂ, κ := ULift.{z} Unit,
    instA := inferInstance, decA := inferInstance, instB := inferInstance,
    instS := inferInstance, starS := inferInstance, instκ := inferInstance,
    M := fun _ _ _ => 1, N := fun _ _ _ => 1 }
  have hp : tpCondition p := by
    simp [tpCondition, p]
  have hbad := h p hp (0 : Matrix p.A p.A p.S)
  exact hbad

theorem dependence.{u, v, w, z} :
    ObservationalDependence signature.{u, v, w, z} actual := by
  intro i
  let p : Parameters.{u, v, w, z} := {
    A := ULift.{u} Unit, B := ULift.{v} Unit, S := ℂ, κ := ULift.{z} Unit,
    instA := inferInstance, decA := inferInstance, instB := inferInstance,
    instS := inferInstance, starS := inferInstance, instκ := inferInstance,
    M := fun _ _ _ => 1, N := fun _ _ _ => 0 }
  refine ⟨p, 0, 1, ?_⟩
  intro he
  have he' := congrArg (fun P : Prop => P) he
  simpa [actual, realize, traceLaw, p, MatrixMap.of_kraus, Matrix.trace,
    Finset.sum_unique] using he'

def source_registration.{u, v, w, z} :
    Registration arena.{u, v, w, z}
      (type_of% (@_root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.IsTracePreserving.of_kraus_isTracePreserving)) where
  actual := actual
  bridge := by
    constructor
    · intro h
      intro A B S κ instA decA instB instS starS instκ M N hTP x
      let p : Parameters.{u, v, w, z} := {
        A := A, B := B, S := S, κ := κ,
        instA := instA, decA := decA, instB := instB,
        instS := instS, starS := starS, instκ := instκ, M := M, N := N }
      have hp : tpCondition p := by simpa [tpCondition, p] using hTP
      have hx := h p hp x
      simpa [actual, realize, traceLaw, p] using hx
    · intro h
      intro A B S κ instA decA instB instS starS instκ M N hTP x
      let p : Parameters.{u, v, w, z} := {
        A := A, B := B, S := S, κ := κ,
        instA := instA, decA := decA, instB := instB,
        instS := instS, starS := starS, instκ := instκ, M := M, N := N }
      have hp : tpCondition p := by simpa [tpCondition, p] using hTP
      have hx := h p hp x
      simpa [actual, realize, traceLaw, p] using hx
  variation := ⟨@_root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.IsTracePreserving.of_kraus_isTracePreserving,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.IsTracePreserving.of_kraus_isTracePreserving)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Foundation.FiniteKrausChannel.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.FiniteKrausChannel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => traceLaw p x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.FiniteKrausChannel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Foundation.FiniteKrausChannel
