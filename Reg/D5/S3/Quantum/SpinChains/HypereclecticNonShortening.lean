import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.HypereclecticNonShortening
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.HypereclecticNonShortening
open _root_.D5.S1.Words.ParityCode.OddTopWeight (ones)

attribute [local instance] LieRing.ofAssociativeRing

namespace Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening

abbrev weightSignature : Signature where
  Params := ℕ
  State N := Fin N → Bool
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
def weightZero : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem weightDependence : ObservationalDependence weightSignature weightActual := by
  intro i
  refine ⟨2, (fun _ => false), (fun j => j == 0), ?_⟩
  norm_num [weightActual, realize, weight, Fin.sum_univ_two]

namespace weight_eq_level

abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ {N : ℕ} (w : Fin N → Bool),
    R.readout () N w = 2 * (level w : ℚ) - (ones w : ℚ) * ((N : ℚ) - ones w)

theorem rejected_law : ¬ arena.Law weightShifted := by
  intro law
  have eq := law (N := 0) (fun i => nomatch i)
  norm_num [weightShifted, realize, weight, level, ones] at eq

def family : Registration arena (type_of% @weight_eq_level) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@weight_eq_level, weightShifted, rejected_law⟩
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
    (@weight_eq_level) (Realization weightSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.weight_eq_level.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.weight_eq_level.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize weightSignature weightActual.readout weightActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.HypereclecticNonShortening
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end weight_eq_level

namespace binSl2Triple

abbrev arena : Arena where
  signature := weightSignature
  Law R := ∀ (N : ℕ) (_hN : 2 ≤ N),
    IsSl2Triple (LinearMap.mulLeft ℚ (fun w : Fin N → Bool => R.readout () N w))
      (Rbin N) (Hbin N)

theorem rejected_law : ¬ arena.Law weightZero := by
  intro law
  have triple := law 2 (by omega)
  exact triple.h_ne_zero (by ext v w; simp [weightZero, realize])

def family : Registration arena (type_of% @binSl2Triple) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@binSl2Triple, weightZero, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weightZero, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := weightDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@binSl2Triple) (Realization weightSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.binSl2Triple.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening.binSl2Triple.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize weightSignature weightActual.readout weightActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.HypereclecticNonShortening
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg", "arg", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end binSl2Triple

end Reg.D5.S3.Quantum.SpinChains.HypereclecticNonShortening
