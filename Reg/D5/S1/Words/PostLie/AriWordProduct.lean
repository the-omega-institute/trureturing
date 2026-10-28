import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.PostLie.AriWordProduct
import Reg.Support.SingleDependentReadout

/-! Source-bound observation families for the original finite ari statements. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S1.Words.PostLie.AriWordProduct
open _root_.D5.S1.Words.PostLie.AriWordOperations
open _root_.D5.S1.Words.PostLie.AriProjection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

open _root_.D5.S1.Words.PostLie.AriWordProduct
open scoped BigOperators
abbrev productSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Word (fun _ => Word) (fun _ => H)
def productActual : Realization productSignature :=
  realize productSignature (fun _ A B => starWord A B) (fun e => nomatch e)
def productRejected : Realization productSignature :=
  realize productSignature (fun _ _ _ => 0) (fun e => nomatch e)
def productWeightRejected : Realization productSignature :=
  realize productSignature (fun _ _ _ => wordBasis (1 : Word)) (fun e => nomatch e)
private theorem starWord_one_one : starWord (1 : Word) 1 = wordBasis 1 := by
  change (∑ f : Fin 0 → Fin 1, orderedTerm 1 (fun j => slot [] f j)) = wordBasis 1
  rw [Fintype.sum_unique]
  simp [orderedTerm, slot]
private theorem starWord_one_letter : starWord (1 : Word) (FreeMonoid.of 0) = letter 0 := by
  change (∑ f : Fin 0 → Fin 2, orderedTerm (FreeMonoid.of 0) (fun j => slot [] f j)) = letter 0
  rw [Fintype.sum_unique]
  simp only [orderedTerm, slot, FreeMonoid.toList_of, List.length_singleton,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    List.get_eq_getElem, List.getElem_singleton, letterAction, ite_true]
  change (1 : H) * letter 0 = letter 0
  exact one_mul _

def productUnshuffleArena : Arena where
  signature := productSignature
  Law R := ∀ A B : Word, R.readout () A B = ((MonoidAlgebra.basis (Fin (B.toList.length + 1) → Word) ℚ).constr ℚ (orderedTerm B)) (primitiveUnshuffle (B.toList.length + 1) A)

private theorem productUnshuffle_rejected : ¬ productUnshuffleArena.Law productRejected := by
  intro h
  have hc := h 1 1
  change (0 : H) = _ at hc
  rw [← starWord_unshuffle, starWord_one_one] at hc
  have hd := congrArg (fun p : H => p.coeff 1) hc
  simp [wordBasis] at hd

def productUnshuffleFamily : Registration productUnshuffleArena (∀ A B : Word, starWord A B = ((MonoidAlgebra.basis (Fin (B.toList.length + 1) → Word) ℚ).constr ℚ (orderedTerm B)) (primitiveUnshuffle (B.toList.length + 1) A)) where
  actual := productActual
  bridge := Iff.rfl
  variation := ⟨starWord_unshuffle, productRejected, productUnshuffle_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ productUnshuffle_rejected
  dependence := by
    change ObservationalDependence productSignature productActual
    intro i
    refine ⟨(1 : Word), (1 : Word), FreeMonoid.of 0, ?_⟩
    change starWord 1 1 ≠ starWord 1 (FreeMonoid.of 0)
    rw [starWord_one_one, starWord_one_letter]
    intro h
    have hw := congrArg weight (wordBasis.injective h)
    simp [gamma] at hw

def productUnshuffleAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriWordProduct.starWord_unshuffle) (Realization productSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordProduct.productUnshuffleUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordProduct.productUnshuffleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨productUnshuffleArena⟩
  objectArena := .source ⟨productUnshuffleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productUnshuffleArena ⟨productUnshuffleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some productActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordProduct
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

def starBasisArena : Arena where
  signature := productSignature
  Law R := ∀ A B : Word, star (wordBasis A) (wordBasis B) = R.readout () A B

private theorem starBasis_rejected : ¬ starBasisArena.Law productRejected := by
  intro h
  have hc := h 1 1
  change star (wordBasis 1) (wordBasis 1) = 0 at hc
  rw [star_basis, starWord_one_one] at hc
  have hd := congrArg (fun p : H => p.coeff 1) hc
  simp [wordBasis] at hd

def starBasisFamily : Registration starBasisArena (∀ A B : Word, star (wordBasis A) (wordBasis B) = starWord A B) where
  actual := productActual
  bridge := Iff.rfl
  variation := ⟨star_basis, productRejected, starBasis_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ starBasis_rejected
  dependence := by
    change ObservationalDependence productSignature productActual
    intro i
    refine ⟨(1 : Word), (1 : Word), FreeMonoid.of 0, ?_⟩
    change starWord 1 1 ≠ starWord 1 (FreeMonoid.of 0)
    rw [starWord_one_one, starWord_one_letter]
    intro h
    have hw := congrArg weight (wordBasis.injective h)
    simp [gamma] at hw

def starBasisAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriWordProduct.star_basis) (Realization productSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordProduct.starBasisUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordProduct.starBasisFamily
  realizationSource := none
  generated := false
  arena := .source ⟨starBasisArena⟩
  objectArena := .source ⟨starBasisArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source starBasisArena ⟨starBasisFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some productActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordProduct
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

def productHomogeneousArena : Arena where
  signature := productSignature
  Law R := ∀ A B : Word, R.readout () A B ∈ homogeneous (weight A + weight B)

private theorem productHomogeneous_rejected : ¬ productHomogeneousArena.Law productWeightRejected := by
  intro h
  have hb := h 1 (FreeMonoid.of 0)
  change wordBasis (1 : Word) ∈ homogeneous 1 at hb
  have hc := hb 1 (by simp [wordBasis])
  change weight (1 : Word) = 1 at hc
  simp at hc

def productHomogeneousFamily : Registration productHomogeneousArena (∀ A B : Word, starWord A B ∈ homogeneous (weight A + weight B)) where
  actual := productActual
  bridge := Iff.rfl
  variation := ⟨starWord_homogeneous, productWeightRejected, productHomogeneous_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ productHomogeneous_rejected
  dependence := by
    change ObservationalDependence productSignature productActual
    intro i
    refine ⟨(1 : Word), (1 : Word), FreeMonoid.of 0, ?_⟩
    change starWord 1 1 ≠ starWord 1 (FreeMonoid.of 0)
    rw [starWord_one_one, starWord_one_letter]
    intro h
    have hw := congrArg weight (wordBasis.injective h)
    simp [gamma] at hw

def productHomogeneousAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriWordProduct.starWord_homogeneous) (Realization productSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordProduct.productHomogeneousUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordProduct.productHomogeneousFamily
  realizationSource := none
  generated := false
  arena := .source ⟨productHomogeneousArena⟩
  objectArena := .source ⟨productHomogeneousArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productHomogeneousArena ⟨productHomogeneousFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some productActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordProduct
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

def productAboveArena : Arena where
  signature := productSignature
  Law R := ∀ (k : ℕ) (A B : Word), R.readout () A B ∈ above k (level k B)

private theorem productAbove_rejected : ¬ productAboveArena.Law productWeightRejected := by
  intro h
  have hb := h 0 1 (FreeMonoid.of 1)
  change wordBasis (1 : Word) ∈ above 0 (level 0 (FreeMonoid.of 1)) at hb
  have hc := hb 1 (by simp [wordBasis])
  change level 0 (FreeMonoid.of 1) ≤ level 0 (1 : Word) at hc
  simp at hc

def productAboveFamily : Registration productAboveArena (∀ (k : ℕ) (A B : Word), starWord A B ∈ above k (level k B)) where
  actual := productActual
  bridge := Iff.rfl
  variation := ⟨starWord_above, productWeightRejected, productAbove_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ productAbove_rejected
  dependence := by
    change ObservationalDependence productSignature productActual
    intro i
    refine ⟨(1 : Word), (1 : Word), FreeMonoid.of 0, ?_⟩
    change starWord 1 1 ≠ starWord 1 (FreeMonoid.of 0)
    rw [starWord_one_one, starWord_one_letter]
    intro h
    have hw := congrArg weight (wordBasis.injective h)
    simp [gamma] at hw

def productAboveAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriWordProduct.starWord_above) (Realization productSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordProduct.productAboveUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordProduct.productAboveFamily
  realizationSource := none
  generated := false
  arena := .source ⟨productAboveArena⟩
  objectArena := .source ⟨productAboveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productAboveArena ⟨productAboveFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some productActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordProduct
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev unshuffleSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Word)
    (fun n => MonoidAlgebra ℚ (Fin n → Word))
def unshuffleActual : Realization unshuffleSignature :=
  realize unshuffleSignature (fun _ n A => primitiveUnshuffle n A) (fun e => nomatch e)
def unshuffleRejected : Realization unshuffleSignature :=
  realize unshuffleSignature (fun _ _ _ => 0) (fun e => nomatch e)

def unshuffleAssignmentsArena : Arena where
  signature := unshuffleSignature
  Law R := ∀ (n : ℕ) (A : List ℕ), R.readout () n (FreeMonoid.ofList A) = ∑ f : Fin A.length → Fin n, MonoidAlgebra.single (fun j => slot A f j) 1

private theorem unshuffleAssignments_rejected : ¬ unshuffleAssignmentsArena.Law unshuffleRejected := by
  intro h
  have hc := h 1 []
  change (0 : MonoidAlgebra ℚ (Fin 1 → Word)) = _ at hc
  have hd := congrArg (fun p : MonoidAlgebra ℚ (Fin 1 → Word) => p.coeff (fun _ => 1)) hc
  simp [slot] at hd

def unshuffleAssignmentsFamily : Registration unshuffleAssignmentsArena (∀ (n : ℕ) (A : List ℕ), primitiveUnshuffle n (FreeMonoid.ofList A) = ∑ f : Fin A.length → Fin n, MonoidAlgebra.single (fun j => slot A f j) 1) where
  actual := unshuffleActual
  bridge := Iff.rfl
  variation := ⟨primitiveUnshuffle_assignments, unshuffleRejected, unshuffleAssignments_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ unshuffleAssignments_rejected
  dependence := by
    change ObservationalDependence unshuffleSignature unshuffleActual
    intro i
    refine ⟨1, (1 : Word), FreeMonoid.of 0, ?_⟩
    change primitiveUnshuffle 1 (1 : Word) ≠ primitiveUnshuffle 1 (FreeMonoid.of 0)
    intro h
    have hc := congrArg (fun p : MonoidAlgebra ℚ (Fin 1 → Word) => p.coeff (fun _ => 1)) h
    have ht : Function.update (fun _ : Fin 1 => (1 : Word)) 0 (FreeMonoid.of 0) ≠ (fun _ => 1) := by
      intro he
      have he0 := congrFun he 0
      simp at he0
    simp [primitiveUnshuffle, MonoidAlgebra.one_def, ht] at hc
    change (1 : MonoidAlgebra ℚ (Fin 1 → Word)).coeff 1 = 0 at hc
    rw [MonoidAlgebra.coeff_one_one] at hc
    exact one_ne_zero hc

def unshuffleAssignmentsAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriWordProduct.primitiveUnshuffle_assignments) (Realization unshuffleSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriWordProduct.unshuffleAssignmentsUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriWordProduct.unshuffleAssignmentsFamily
  realizationSource := none
  generated := false
  arena := .source ⟨unshuffleAssignmentsArena⟩
  objectArena := .source ⟨unshuffleAssignmentsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source unshuffleAssignmentsArena ⟨unshuffleAssignmentsFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some unshuffleActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriWordProduct
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

end Reg.D5.S1.Words.PostLie.AriWordProduct
