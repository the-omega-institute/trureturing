import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Recovery.BKMObservableRigidity

/-! Source-bound readouts of the weighted compression and integrated BKM gap. -/

noncomputable section

universe u
open Matrix MeasureTheory LeanInformationAudit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement (lift bkmGap)
open _root_.D5.S3.Quantum.Recovery.BKMObservableRigidity

namespace Reg.D5.S3.Quantum.Recovery.BKMObservableRigidity

private abbrev equalitySignature (P : Type*) (X : P → Type*) : Signature where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := X p → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def rejectEquality (P : Type*) (X : P → Type*) :
    Realization (equalitySignature P X) :=
  realize (equalitySignature P X) (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependent {P : Type*} {X : P → Type*} (p : P) (x y : X p) (h : x ≠ y) :
    ObservationalDependence (equalitySignature P X)
      (realize (equalitySignature P X) (fun _ _ x y => x = y) (fun e => nomatch e)) := by
  intro role
  refine ⟨p, x, y, ?_⟩
  intro heq
  have hz := congrFun heq y
  change (x = y) = (y = y) at hz
  exact h (hz.mpr rfl)

namespace Compression

private abbrev Carrier (R : Type u) := Matrix (R × R) (R × R) ℂ

private abbrev signature := equalitySignature (Type u) Carrier

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {R E : Type u} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef),
    let V := weightedLift A hA
    (∀ K, V *ᵥ weightedVec (partialTraceRight A) K = weightedVec A (lift K)) ∧
      r.readout () R (Vᴴ * V) 1 ∧ Vᴴ * modular A * V = modular (partialTraceRight A)

private theorem rejected : ¬ arena.{u}.Law (rejectEquality (Type u) Carrier) := by
  intro h
  exact (h (R := ULift.{u} Unit) (E := ULift.{u} Unit) 1 Matrix.PosDef.one).2.1

def family : Registration arena.{u} (type_of% @weightedLift_compression.{u}) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@weightedLift_compression.{u}, rejectEquality _ _, rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejectEquality _ _, ?_, ?_, rejected⟩
      · intro other h
        cases role
        cases other
        exact (h rfl).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    apply dependent (ULift.{u} Unit) 0 (fun _ _ => 1)
    intro h
    exact zero_ne_one (congrFun (congrFun h (⟨()⟩, ⟨()⟩)) (⟨()⟩, ⟨()⟩))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weightedLift_compression.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.BKMObservableRigidity.weightedLift_compression.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMObservableRigidity.Compression.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMObservableRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Compression

namespace Gap

private abbrev signature := equalitySignature Unit (fun _ => ℝ)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {R E : Type u} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E] [Nonempty E]
    (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef) (K : Matrix R R ℂ) (_hK : K.IsHermitian),
    let S := partialTraceRight A
    let V := weightedLift A hA
    let b := weightedVec S K
    r.readout () () (bkmGap A K) (∫ p in (0 : ℝ)..1, powerDefect A hA K p) ∧
      0 ≤ bkmGap A K ∧
      (bkmGap A K = 0 ↔ ∀ f : ℝ → ℝ,
        cfc f (modular A) *ᵥ (V *ᵥ b) = V *ᵥ (cfc f (modular S) *ᵥ b))

private theorem rejected : ¬ arena.{u}.Law (rejectEquality Unit (fun _ => ℝ)) := by
  intro h
  exact (h (R := ULift.{u} Unit) (E := ULift.{u} Unit) 1 Matrix.PosDef.one
    0 Matrix.isHermitian_zero).1

def family : Registration arena.{u} (type_of% @bkmGap_rigidity.{u}) where
  actual := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@bkmGap_rigidity.{u}, rejectEquality _ _, rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejectEquality _ _, ?_, ?_, rejected⟩
      · intro other h
        cases role
        cases other
        exact (h rfl).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependent () (0 : ℝ) 1 zero_ne_one

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bkmGap_rigidity.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMObservableRigidity.bkmGap_rigidity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMObservableRigidity.Gap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMObservableRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Gap

end Reg.D5.S3.Quantum.Recovery.BKMObservableRigidity
