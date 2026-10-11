import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.BinaryBinBaseChange
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.BinaryBinBaseChange
open _root_.D5.S3.Quantum.SpinChains.HypereclecticNonShortening
open _root_.D5.S3.Quantum.SpinChains.Sl2WeightFiltration
open scoped TensorProduct

namespace Reg.D5.S3.Quantum.SpinChains.BinaryBinBaseChange
universe u

abbrev testK := ULift.{u} ℚ
instance testCharZero : CharZero testK.{u} := ⟨fun _m _n eq =>
  (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℚ)))
    (congrArg ULift.down eq)⟩

abbrev weightSignature : Signature where
  Params := ℕ
  State m := Fin m → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ w => weight w) (fun e => nomatch e)
def weightShifted : Realization weightSignature :=
  realize weightSignature (fun _ _ w => weight w + 1) (fun e => nomatch e)

theorem weightDependence : ObservationalDependence weightSignature weightActual := by
  intro i
  refine ⟨2, (fun _ => false), (fun j => j == 0), ?_⟩
  norm_num [weightActual, realize, weight, Fin.sum_univ_two]

namespace bin_action

abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ (K : Type u) [Field K] [CharZero K] (m : ℕ),
    Sl2Relations (binWeight K m) (binRaising K m) (binLowering K m) ∧
    ∀ (w u : Fin m → Bool),
      binWeight K m (Pi.single w 1) u =
        (R.readout () m u : K) * (Pi.single w 1 : _ → K) u ∧
      binRaising K m (Pi.single w 1) u = (Rbin m (Pi.single w 1) u : K) ∧
      binLowering K m (Pi.single w 1) u = (Hbin m (Pi.single w 1) u : K)

theorem rejected_law : ¬ arena.{u}.Law weightShifted := by
  intro law
  let w : Fin 0 → Bool := fun i => nomatch i
  have z := (law testK.{u} 0).2 w w |>.1
  have eq := (bin_action testK.{u} 0).2 w w |>.1
  rw [eq] at z
  norm_num [weightShifted, realize, weight, Pi.single_apply] at z

def family : Registration arena.{u} (type_of% @bin_action.{u}) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@bin_action.{u}, weightShifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weightShifted, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := weightDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@bin_action.{u}) (Realization weightSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.BinaryBinBaseChange.bin_action.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.BinaryBinBaseChange.bin_action.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize weightSignature weightActual.readout weightActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.BinaryBinBaseChange
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end bin_action

namespace two_bin_action

abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ (K : Type u) [Field K] [CharZero K] (m n : ℕ),
    Sl2Relations (twoWeight K m n) (twoRaising K m n) (twoLowering K m n) ∧
    ∀ (w : Fin m → Bool) (v : Fin n → Bool),
      twoWeight K m n (Pi.single w 1 ⊗ₜ[K] Pi.single v 1) =
        ((R.readout () m w : K) + (weight v : K)) •
          (Pi.single w 1 ⊗ₜ[K] Pi.single v 1) ∧
      twoRaising K m n (Pi.single w 1 ⊗ₜ[K] Pi.single v 1) =
        (fun u => (Rbin m (Pi.single w 1) u : K)) ⊗ₜ[K] Pi.single v 1 +
        Pi.single w 1 ⊗ₜ[K] (fun u => (Rbin n (Pi.single v 1) u : K)) ∧
      twoLowering K m n (Pi.single w 1 ⊗ₜ[K] Pi.single v 1) =
        (fun u => (Hbin m (Pi.single w 1) u : K)) ⊗ₜ[K] Pi.single v 1 +
        Pi.single w 1 ⊗ₜ[K] (fun u => (Hbin n (Pi.single v 1) u : K))

theorem rejected_law : ¬ arena.{u}.Law weightShifted := by
  intro law
  let w : Fin 0 → Bool := fun i => nomatch i
  have z := (law testK.{u} 0 0).2 w w |>.1
  have eq := (two_bin_action testK.{u} 0 0).2 w w |>.1
  rw [eq] at z
  have z' := congrArg (fun t =>
    (TensorProduct.piScalarRight testK testK ((Fin 0 → Bool) → testK)
      (Fin 0 → Bool) t) w w) z
  norm_num [weightShifted, realize, weight, Pi.single_apply,
    TensorProduct.piScalarRightHom_tmul] at z'

def family : Registration arena.{u} (type_of% @two_bin_action.{u}) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@two_bin_action.{u}, weightShifted, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weightShifted, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := weightDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@two_bin_action.{u}) (Realization weightSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.BinaryBinBaseChange.two_bin_action.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.BinaryBinBaseChange.two_bin_action.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize weightSignature weightActual.readout weightActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.BinaryBinBaseChange
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end two_bin_action

end Reg.D5.S3.Quantum.SpinChains.BinaryBinBaseChange
