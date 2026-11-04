import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords
import Reg.Support.DependentFamily

/-! Source-bound audit of the dimension of binary bond-two trace coordinates. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords
open _root_.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords
open _root_.D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation (traceWord)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the equality relation on the two natural dimension operands. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Preserve every word length, trace coordinate, and weighted exponent constraint. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    R.readout () ()
      (Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : Fin n → Fin 2 =>
        fun p : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ => traceWord 2 2 n p i)))
      ((n + 1) + Fintype.card {e : Fin 5 → Fin (n + 1) //
        (e 0).val + (e 1).val + 2 * (e 2).val + 2 * (e 3).val + 2 * (e 4).val + 4 = n})

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1

def source_registration : Registration arena (type_of% @coordinate_dimension) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coordinate_dimension, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hbad : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hbad

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords.coordinate_dimension)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.TensorNetworks.UniformMPSTwoByTwoTraceWords
