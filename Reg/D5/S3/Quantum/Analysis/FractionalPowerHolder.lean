import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.FractionalPowerHolder
import Reg.Support.DependentFamily
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Order

/-! Source-bound real comparison for the full positive-cone Hölder estimate. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open QuantumFractionalPower LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.FractionalPowerHolder

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The carrier, all three structures, both positive inputs, and the complete
exponent interval remain in the source law. Only the final comparison varies. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1),
    R.readout () () ‖CFC.rpow a p - CFC.rpow b p‖ (‖a - b‖ ^ p)

private theorem actual_law : arena.{u}.Law actual :=
  @norm_rpow_sub_rpow_le.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A := CStarMatrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ
  exact h (A := A) (a := 0) (b := 0) le_rfl le_rfl
    (p := 1) zero_lt_one le_rfl

def family : Registration arena.{u} (type_of% (@norm_rpow_sub_rpow_le.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_rpow_sub_rpow_le.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.FractionalPowerHolder.holderUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.FractionalPowerHolder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.FractionalPowerHolder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Analysis.FractionalPowerHolder
