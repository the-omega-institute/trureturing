import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.PostLie.AriWordOperations
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of original weights, levels, support and letter actions. -/
set_option autoImplicit false
noncomputable section

namespace Reg.D5.S1.Words.PostLie.AriWordOperations
open _root_.D5.S1.Words.PostLie.AriWordOperations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev weightSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Word) (fun _ => ℕ)

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ w => weight w) (fun e => nomatch e)

def weightRejected : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 1) (fun e => nomatch e)

def weightOneArena : Arena where
  signature := weightSignature
  Law R := R.readout () () (1 : Word) = 0

private theorem weightOne_rejected : ¬ weightOneArena.Law weightRejected := by
  change ¬ (1 : ℕ) = 0
  omega

def weightOneFamily : Registration weightOneArena (weight (1 : Word) = 0) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨weight_one, weightRejected, weightOne_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ weightOne_rejected
  dependence := by
    change ObservationalDependence weightSignature weightActual
    intro i
    refine ⟨(), (1 : Word), FreeMonoid.of 0, ?_⟩
    change weight (1 : Word) ≠ weight (FreeMonoid.of 0)
    simp [gamma]

def weightOneAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weight_one) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.weightOneUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.weightOneFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weightOneArena⟩
  objectArena := .source ⟨weightOneArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightOneArena ⟨weightOneFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ w => weight w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


def weightMulArena : Arena where
  signature := weightSignature
  Law R := ∀ u v : Word, R.readout () () (u * v) = weight u + weight v

private theorem weightMul_rejected : ¬ weightMulArena.Law weightRejected := by
  intro h
  have hb := h 1 1
  change (1 : ℕ) = 0 + 0 at hb
  omega

def weightMulFamily : Registration weightMulArena (∀ u v : Word, weight (u * v) = weight u + weight v) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨weight_mul, weightRejected, weightMul_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ weightMul_rejected
  dependence := by
    change ObservationalDependence weightSignature weightActual
    intro i
    refine ⟨(), (1 : Word), FreeMonoid.of 0, ?_⟩
    change weight (1 : Word) ≠ weight (FreeMonoid.of 0)
    simp [gamma]

def weightMulAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weight_mul) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.weightMulUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.weightMulFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weightMulArena⟩
  objectArena := .source ⟨weightMulArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightMulArena ⟨weightMulFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ w => weight w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def weightOfArena : Arena where
  signature := weightSignature
  Law R := ∀ s : ℕ, R.readout () () (FreeMonoid.of s) = gamma s

private theorem weightOf_rejected : ¬ weightOfArena.Law weightRejected := by
  intro h
  have hb := h 2
  change (1 : ℕ) = gamma 2 at hb
  norm_num [gamma] at hb

def weightOfFamily : Registration weightOfArena (∀ s : ℕ, weight (FreeMonoid.of s) = gamma s) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨weight_of, weightRejected, weightOf_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ weightOf_rejected
  dependence := by
    change ObservationalDependence weightSignature weightActual
    intro i
    refine ⟨(), (1 : Word), FreeMonoid.of 0, ?_⟩
    change weight (1 : Word) ≠ weight (FreeMonoid.of 0)
    simp [gamma]

def weightOfAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weight_of) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.weightOfUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.weightOfFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weightOfArena⟩
  objectArena := .source ⟨weightOfArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightOfArena ⟨weightOfFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ w => weight w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev levelSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Word) (fun _ => ℕ)
def levelActual : Realization levelSignature :=
  realize levelSignature (fun _ k w => level k w) (fun e => nomatch e)
def levelRejected : Realization levelSignature :=
  realize levelSignature (fun _ _ _ => 2) (fun e => nomatch e)

def levelOneArena : Arena where
  signature := levelSignature
  Law R := ∀ k : ℕ, R.readout () k (1 : Word) = 0

private theorem levelOne_rejected : ¬ levelOneArena.Law levelRejected := by
  intro h
  have hb := h 0
  change (2 : ℕ) = 0 at hb
  omega

def levelOneFamily : Registration levelOneArena (∀ k : ℕ, level k (1 : Word) = 0) where
  actual := levelActual
  bridge := Iff.rfl
  variation := ⟨level_one, levelRejected, levelOne_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ levelOne_rejected
  dependence := by
    change ObservationalDependence levelSignature levelActual
    intro i
    refine ⟨0, (1 : Word), FreeMonoid.of 1, ?_⟩
    change level 0 (1 : Word) ≠ level 0 (FreeMonoid.of 1)
    simp

def levelOneAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@level_one) (Realization levelSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.levelOneUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.levelOneFamily
  realizationSource := none
  generated := false
  arena := .source ⟨levelOneArena⟩
  objectArena := .source ⟨levelOneArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source levelOneArena ⟨levelOneFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize levelSignature (fun _ k w => level k w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def levelMulArena : Arena where
  signature := levelSignature
  Law R := ∀ (k : ℕ) (u v : Word), R.readout () k (u * v) = level k u + level k v

private theorem levelMul_rejected : ¬ levelMulArena.Law levelRejected := by
  intro h
  have hb := h 0 1 1
  change (2 : ℕ) = 0 + 0 at hb
  omega

def levelMulFamily : Registration levelMulArena (∀ (k : ℕ) (u v : Word), level k (u * v) = level k u + level k v) where
  actual := levelActual
  bridge := Iff.rfl
  variation := ⟨level_mul, levelRejected, levelMul_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ levelMul_rejected
  dependence := by
    change ObservationalDependence levelSignature levelActual
    intro i
    refine ⟨0, (1 : Word), FreeMonoid.of 1, ?_⟩
    change level 0 (1 : Word) ≠ level 0 (FreeMonoid.of 1)
    simp

def levelMulAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@level_mul) (Realization levelSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.levelMulUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.levelMulFamily
  realizationSource := none
  generated := false
  arena := .source ⟨levelMulArena⟩
  objectArena := .source ⟨levelMulArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source levelMulArena ⟨levelMulFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize levelSignature (fun _ k w => level k w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def levelOfArena : Arena where
  signature := levelSignature
  Law R := ∀ k s : ℕ, R.readout () k (FreeMonoid.of s) = if s = k then 0 else 1

private theorem levelOf_rejected : ¬ levelOfArena.Law levelRejected := by
  intro h
  have hb := h 0 0
  change (2 : ℕ) = (if (0 : ℕ) = 0 then 0 else 1) at hb
  norm_num at hb

def levelOfFamily : Registration levelOfArena (∀ k s : ℕ, level k (FreeMonoid.of s) = if s = k then 0 else 1) where
  actual := levelActual
  bridge := Iff.rfl
  variation := ⟨level_of, levelRejected, levelOf_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ levelOf_rejected
  dependence := by
    change ObservationalDependence levelSignature levelActual
    intro i
    refine ⟨0, (1 : Word), FreeMonoid.of 1, ?_⟩
    change level 0 (1 : Word) ≠ level 0 (FreeMonoid.of 1)
    simp

def levelOfAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@level_of) (Realization levelSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.levelOfUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.levelOfFamily
  realizationSource := none
  generated := false
  arena := .source ⟨levelOfArena⟩
  objectArena := .source ⟨levelOfArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source levelOfArena ⟨levelOfFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize levelSignature (fun _ k w => level k w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev basisSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Word) (fun _ => H)
def basisActual : Realization basisSignature :=
  realize basisSignature (fun _ _ w => wordBasis w) (fun e => nomatch e)
def basisRejected : Realization basisSignature :=
  realize basisSignature (fun _ _ _ => wordBasis (FreeMonoid.of 0)) (fun e => nomatch e)

def homogeneousBasisArena : Arena where
  signature := basisSignature
  Law R := ∀ w : Word, R.readout () () w ∈ homogeneous (weight w)

private theorem homogeneousBasis_rejected : ¬ homogeneousBasisArena.Law basisRejected := by
  intro h
  have hb := h 1
  change wordBasis (FreeMonoid.of 0) ∈ homogeneous 0 at hb
  have hc := hb (FreeMonoid.of 0) (by simp [wordBasis])
  change weight (FreeMonoid.of 0) = 0 at hc
  simp [gamma] at hc

def homogeneousBasisFamily : Registration homogeneousBasisArena (∀ w : Word, wordBasis w ∈ homogeneous (weight w)) where
  actual := basisActual
  bridge := Iff.rfl
  variation := ⟨homogeneous_basis, basisRejected, homogeneousBasis_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ homogeneousBasis_rejected
  dependence := by
    change ObservationalDependence basisSignature basisActual
    intro i
    refine ⟨(), (1 : Word), FreeMonoid.of 0, ?_⟩
    change wordBasis (1 : Word) ≠ wordBasis (FreeMonoid.of 0)
    intro h
    have hw := congrArg weight (wordBasis.injective h)
    simp [gamma] at hw

def homogeneousBasisAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@homogeneous_basis) (Realization basisSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.homogeneousBasisUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.homogeneousBasisFamily
  realizationSource := none
  generated := false
  arena := .source ⟨homogeneousBasisArena⟩
  objectArena := .source ⟨homogeneousBasisArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source homogeneousBasisArena ⟨homogeneousBasisFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize basisSignature (fun _ _ w => wordBasis w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def aboveBasisArena : Arena where
  signature := basisSignature
  Law R := ∀ (k : ℕ) (w : Word), R.readout () () w ∈ above k (level k w)

private theorem aboveBasis_rejected : ¬ aboveBasisArena.Law basisRejected := by
  intro h
  have hb := h 0 (FreeMonoid.of 1)
  change wordBasis (FreeMonoid.of 0) ∈ above 0 (level 0 (FreeMonoid.of 1)) at hb
  have hc := hb (FreeMonoid.of 0) (by simp [wordBasis])
  change level 0 (FreeMonoid.of 1) ≤ level 0 (FreeMonoid.of 0) at hc
  simp at hc

def aboveBasisFamily : Registration aboveBasisArena (∀ (k : ℕ) (w : Word), wordBasis w ∈ above k (level k w)) where
  actual := basisActual
  bridge := Iff.rfl
  variation := ⟨above_basis, basisRejected, aboveBasis_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ aboveBasis_rejected
  dependence := by
    change ObservationalDependence basisSignature basisActual
    intro i
    refine ⟨(), (1 : Word), FreeMonoid.of 0, ?_⟩
    change wordBasis (1 : Word) ≠ wordBasis (FreeMonoid.of 0)
    intro h
    have hw := congrArg weight (wordBasis.injective h)
    simp [gamma] at hw

def aboveBasisAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@above_basis) (Realization basisSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.aboveBasisUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.aboveBasisFamily
  realizationSource := none
  generated := false
  arena := .source ⟨aboveBasisArena⟩
  objectArena := .source ⟨aboveBasisArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source aboveBasisArena ⟨aboveBasisFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize basisSignature (fun _ _ w => wordBasis w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev mulSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature H (fun _ => H) (fun _ => H)
def mulActual : Realization mulSignature :=
  realize mulSignature (fun _ p q => p * q) (fun e => nomatch e)
def homogeneousMulRejected : Realization mulSignature :=
  realize mulSignature (fun _ _ _ => wordBasis (FreeMonoid.of 0)) (fun e => nomatch e)
def aboveMulRejected : Realization mulSignature :=
  realize mulSignature (fun _ _ _ => wordBasis (1 : Word)) (fun e => nomatch e)

def homogeneousMulArena : Arena where
  signature := mulSignature
  Law R := ∀ (p q : H) (a b : ℕ), p ∈ homogeneous a → q ∈ homogeneous b → R.readout () p q ∈ homogeneous (a + b)

private theorem homogeneousMul_rejected : ¬ homogeneousMulArena.Law homogeneousMulRejected := by
  intro h
  have hb := h 0 0 0 0 (Submodule.zero_mem _) (Submodule.zero_mem _)
  change wordBasis (FreeMonoid.of 0) ∈ homogeneous 0 at hb
  have hc := hb (FreeMonoid.of 0) (by simp [wordBasis])
  change weight (FreeMonoid.of 0) = 0 at hc
  simp [gamma] at hc

def homogeneousMulFamily : Registration homogeneousMulArena (∀ (p q : H) (a b : ℕ), p ∈ homogeneous a → q ∈ homogeneous b → p * q ∈ homogeneous (a + b)) where
  actual := mulActual
  bridge := Iff.rfl
  variation := ⟨homogeneous_mul, homogeneousMulRejected, homogeneousMul_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ homogeneousMul_rejected
  dependence := by
    change ObservationalDependence mulSignature mulActual
    intro i
    refine ⟨(1 : H), (0 : H), (1 : H), ?_⟩
    change (1 : H) * 0 ≠ 1 * 1
    simp

def homogeneousMulAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@homogeneous_mul) (Realization mulSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.homogeneousMulUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.homogeneousMulFamily
  realizationSource := none
  generated := false
  arena := .source ⟨homogeneousMulArena⟩
  objectArena := .source ⟨homogeneousMulArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source homogeneousMulArena ⟨homogeneousMulFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize mulSignature (fun _ p q => p * q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def aboveMulArena : Arena where
  signature := mulSignature
  Law R := ∀ (k : ℕ) (p q : H) (a b : ℕ), p ∈ above k a → q ∈ above k b → R.readout () p q ∈ above k (a + b)

private theorem aboveMul_rejected : ¬ aboveMulArena.Law aboveMulRejected := by
  intro h
  have hp : wordBasis (FreeMonoid.of 1) ∈ above 0 1 := by simpa using above_basis 0 (FreeMonoid.of 1)
  have hb := h 0 (wordBasis (FreeMonoid.of 1)) (wordBasis 1) 1 0 hp (above_basis 0 1)
  change wordBasis (1 : Word) ∈ above 0 1 at hb
  have hc := hb 1 (by simp [wordBasis])
  change 1 ≤ level 0 (1 : Word) at hc
  simp at hc

def aboveMulFamily : Registration aboveMulArena (∀ (k : ℕ) (p q : H) (a b : ℕ), p ∈ above k a → q ∈ above k b → p * q ∈ above k (a + b)) where
  actual := mulActual
  bridge := Iff.rfl
  variation := ⟨above_mul, aboveMulRejected, aboveMul_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ aboveMul_rejected
  dependence := by
    change ObservationalDependence mulSignature mulActual
    intro i
    refine ⟨(1 : H), (0 : H), (1 : H), ?_⟩
    change (1 : H) * 0 ≠ 1 * 1
    simp

def aboveMulAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@above_mul) (Realization mulSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.aboveMulUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.aboveMulFamily
  realizationSource := none
  generated := false
  arena := .source ⟨aboveMulArena⟩
  objectArena := .source ⟨aboveMulArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source aboveMulArena ⟨aboveMulFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize mulSignature (fun _ p q => p * q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev actionSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Word (fun _ => ℕ) (fun _ => H)
def actionActual : Realization actionSignature :=
  realize actionSignature (fun _ A s => letterAction A s) (fun e => nomatch e)
def actionRejected : Realization actionSignature :=
  realize actionSignature (fun _ _ _ => wordBasis (1 : Word)) (fun e => nomatch e)

def actionHomogeneousArena : Arena where
  signature := actionSignature
  Law R := ∀ (A : Word) (s : ℕ), R.readout () A s ∈ homogeneous (weight A + gamma s)

private theorem actionHomogeneous_rejected : ¬ actionHomogeneousArena.Law actionRejected := by
  intro h
  have hb := h 1 0
  change wordBasis (1 : Word) ∈ homogeneous 1 at hb
  have hc := hb 1 (by simp [wordBasis])
  change weight (1 : Word) = 1 at hc
  simp at hc

def actionHomogeneousFamily : Registration actionHomogeneousArena (∀ (A : Word) (s : ℕ), letterAction A s ∈ homogeneous (weight A + gamma s)) where
  actual := actionActual
  bridge := Iff.rfl
  variation := ⟨letterAction_homogeneous, actionRejected, actionHomogeneous_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ actionHomogeneous_rejected
  dependence := by
    change ObservationalDependence actionSignature actionActual
    intro i
    refine ⟨(1 : Word), (0 : ℕ), (1 : ℕ), ?_⟩
    change letterAction 1 0 ≠ letterAction 1 1
    simp only [letterAction, ite_true, letter]
    intro h
    have hw := FreeMonoid.of_injective (wordBasis.injective h)
    omega

def actionHomogeneousAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@letterAction_homogeneous) (Realization actionSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordOperations.actionHomogeneousUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordOperations.actionHomogeneousFamily
  realizationSource := none
  generated := false
  arena := .source ⟨actionHomogeneousArena⟩
  objectArena := .source ⟨actionHomogeneousArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source actionHomogeneousArena ⟨actionHomogeneousFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize actionSignature (fun _ A s => letterAction A s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordOperations
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.PostLie.AriWordOperations
