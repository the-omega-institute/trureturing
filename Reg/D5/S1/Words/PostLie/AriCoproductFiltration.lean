import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.PostLie.AriCoproductFiltration
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the full ordinary ari transpose and its filtration. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S1.Words.PostLie.AriCoproductFiltration
open _root_.D5.S1.Words.PostLie.AriWordOperations
open _root_.D5.S1.Words.PostLie.AriWordProduct
open _root_.D5.S1.Words.PostLie.AriCoproductFiltration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators TensorProduct

abbrev windowSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Finset Word)
def windowActual : Realization windowSignature :=
  realize windowSignature (fun _ _ n => weightWindow n) (fun e => nomatch e)
def windowRejected : Realization windowSignature :=
  realize windowSignature (fun _ _ _ => ∅) (fun e => nomatch e)

def windowMembershipArena : Arena where
  signature := windowSignature
  Law R := ∀ (N : ℕ) (w : Word), w ∈ R.readout () () N ↔ weight w ≤ N

private theorem windowMembership_rejected : ¬ windowMembershipArena.Law windowRejected := by
  intro h
  have hc := (h 0 1).mpr (by simp)
  change (1 : Word) ∈ (∅ : Finset Word) at hc
  exact Finset.notMem_empty _ hc

def windowMembershipFamily : Registration windowMembershipArena (∀ (N : ℕ) (w : Word), w ∈ weightWindow N ↔ weight w ≤ N) where
  actual := windowActual
  bridge := Iff.rfl
  variation := ⟨mem_weightWindow, windowRejected, windowMembership_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ windowMembership_rejected
  dependence := by
    change ObservationalDependence windowSignature windowActual
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change weightWindow 0 ≠ weightWindow 1
    intro he
    have hm : FreeMonoid.of 0 ∈ weightWindow 1 := by simp [mem_weightWindow, gamma]
    rw [← he] at hm
    simp [mem_weightWindow, gamma] at hm

def windowMembershipAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriCoproductFiltration.mem_weightWindow) (Realization windowSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.windowMembershipUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.windowMembershipFamily
  realizationSource := none
  generated := false
  arena := .source ⟨windowMembershipArena⟩
  objectArena := .source ⟨windowMembershipArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source windowMembershipArena ⟨windowMembershipFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize windowSignature (fun _ _ n => weightWindow n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriCoproductFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev transposeSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => H) (fun _ => H ⊗[ℚ] H)
def transposeActual : Realization transposeSignature :=
  realize transposeSignature (fun _ _ P => delta P) (fun e => nomatch e)
def transposeRejected : Realization transposeSignature :=
  realize transposeSignature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem starWord_one_one : starWord (1 : Word) 1 = wordBasis 1 := by
  change (∑ f : Fin 0 → Fin 1, orderedTerm 1 (fun j => slot [] f j)) = wordBasis 1
  rw [Fintype.sum_unique]
  simp [orderedTerm, slot]

def fullTransposeArena : Arena where
  signature := transposeSignature
  Law S := ∀ P Q R : H, tensorPairing Q R (S.readout () () P) = pairing P (star Q R)

private theorem fullTranspose_rejected : ¬ fullTransposeArena.Law transposeRejected := by
  intro h
  have hc := h (wordBasis 1) (wordBasis 1) (wordBasis 1)
  change tensorPairing (wordBasis 1) (wordBasis 1) 0 = pairing (wordBasis 1) (star (wordBasis 1) (wordBasis 1)) at hc
  rw [map_zero, star_basis, starWord_one_one] at hc
  rw [pairing_basis] at hc
  simp [wordBasis] at hc

def fullTransposeFamily : Registration fullTransposeArena (∀ P Q R : H, tensorPairing Q R (delta P) = pairing P (star Q R)) where
  actual := transposeActual
  bridge := Iff.rfl
  variation := ⟨delta_transpose, transposeRejected, fullTranspose_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ fullTranspose_rejected
  dependence := by
    change ObservationalDependence transposeSignature transposeActual
    intro i
    refine ⟨(), (0 : H), wordBasis (1 : Word), ?_⟩
    change delta 0 ≠ delta (wordBasis 1)
    intro he
    have hc := congrArg (fun T : H ⊗[ℚ] H => tensorBasis.repr T (1, 1)) he
    simp only [map_zero, Finsupp.zero_apply] at hc
    rw [delta_basis_coefficient, starWord_one_one] at hc
    simp [wordBasis] at hc

def fullTransposeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriCoproductFiltration.delta_transpose) (Realization transposeSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.fullTransposeUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.fullTransposeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fullTransposeArena⟩
  objectArena := .source ⟨fullTransposeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fullTransposeArena ⟨fullTransposeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transposeSignature (fun _ _ P => delta P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriCoproductFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def transposeCoefficientArena : Arena where
  signature := transposeSignature
  Law R := ∀ (P : H) (A B : Word), tensorBasis.repr (R.readout () () P) (A, B) = pairing P (star (wordBasis A) (wordBasis B))

private theorem transposeCoefficient_rejected : ¬ transposeCoefficientArena.Law transposeRejected := by
  intro h
  have hc := h (wordBasis 1) 1 1
  change tensorBasis.repr 0 (1, 1) = pairing (wordBasis 1) (star (wordBasis 1) (wordBasis 1)) at hc
  rw [map_zero, Finsupp.zero_apply, star_basis, starWord_one_one] at hc
  rw [pairing_basis] at hc
  simp [wordBasis] at hc

def transposeCoefficientFamily : Registration transposeCoefficientArena (∀ (P : H) (A B : Word), tensorBasis.repr (delta P) (A, B) = pairing P (star (wordBasis A) (wordBasis B))) where
  actual := transposeActual
  bridge := Iff.rfl
  variation := ⟨delta_coefficient, transposeRejected, transposeCoefficient_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ transposeCoefficient_rejected
  dependence := by
    change ObservationalDependence transposeSignature transposeActual
    intro i
    refine ⟨(), (0 : H), wordBasis (1 : Word), ?_⟩
    change delta 0 ≠ delta (wordBasis 1)
    intro he
    have hc := congrArg (fun T : H ⊗[ℚ] H => tensorBasis.repr T (1, 1)) he
    simp only [map_zero, Finsupp.zero_apply] at hc
    rw [delta_basis_coefficient, starWord_one_one] at hc
    simp [wordBasis] at hc

def transposeCoefficientAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriCoproductFiltration.delta_coefficient) (Realization transposeSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.transposeCoefficientUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.transposeCoefficientFamily
  realizationSource := none
  generated := false
  arena := .source ⟨transposeCoefficientArena⟩
  objectArena := .source ⟨transposeCoefficientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transposeCoefficientArena ⟨transposeCoefficientFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transposeSignature (fun _ _ P => delta P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriCoproductFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def transposeBasisCoefficientArena : Arena where
  signature := transposeSignature
  Law R := ∀ w A B : Word, tensorBasis.repr (R.readout () () (wordBasis w)) (A, B) = (starWord A B).coeff w

private theorem transposeBasisCoefficient_rejected : ¬ transposeBasisCoefficientArena.Law transposeRejected := by
  intro h
  have hc := h 1 1 1
  change tensorBasis.repr 0 (1, 1) = (starWord 1 1).coeff 1 at hc
  rw [map_zero, Finsupp.zero_apply, starWord_one_one] at hc
  simp [wordBasis] at hc

def transposeBasisCoefficientFamily : Registration transposeBasisCoefficientArena (∀ w A B : Word, tensorBasis.repr (delta (wordBasis w)) (A, B) = (starWord A B).coeff w) where
  actual := transposeActual
  bridge := Iff.rfl
  variation := ⟨delta_basis_coefficient, transposeRejected, transposeBasisCoefficient_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ transposeBasisCoefficient_rejected
  dependence := by
    change ObservationalDependence transposeSignature transposeActual
    intro i
    refine ⟨(), (0 : H), wordBasis (1 : Word), ?_⟩
    change delta 0 ≠ delta (wordBasis 1)
    intro he
    have hc := congrArg (fun T : H ⊗[ℚ] H => tensorBasis.repr T (1, 1)) he
    simp only [map_zero, Finsupp.zero_apply] at hc
    rw [delta_basis_coefficient, starWord_one_one] at hc
    simp [wordBasis] at hc

def transposeBasisCoefficientAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriCoproductFiltration.delta_basis_coefficient) (Realization transposeSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.transposeBasisCoefficientUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.transposeBasisCoefficientFamily
  realizationSource := none
  generated := false
  arena := .source ⟨transposeBasisCoefficientArena⟩
  objectArena := .source ⟨transposeBasisCoefficientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transposeBasisCoefficientArena ⟨transposeBasisCoefficientFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transposeSignature (fun _ _ P => delta P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriCoproductFiltration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def filtrationRejected : Realization transposeSignature :=
  realize transposeSignature
    (fun _ _ _ => wordBasis (1 : Word) ⊗ₜ[ℚ] wordBasis (FreeMonoid.of 1))
    (fun e => nomatch e)

private theorem forbidden_tensor :
    wordBasis (1 : Word) ⊗ₜ[ℚ] wordBasis (FreeMonoid.of 1) ∉ rightFiltrationImage 0 0 := by
  let f : H →ₗ[ℚ] ℚ := (Finsupp.lapply (FreeMonoid.of 1)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap
  have hs : filtration 0 0 ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    change (wordBasis w).coeff (FreeMonoid.of 1) = 0
    by_cases he : w = FreeMonoid.of 1
    · subst w
      simp at hw
    · simp [wordBasis, MonoidAlgebra.coeff_single, he]
  have hf (b : filtration 0 0) : f b.val = 0 := hs b.property
  let L : (H ⊗[ℚ] H) →ₗ[ℚ] ℚ :=
    TensorProduct.lift ((pairing (wordBasis 1)).smulRight f)
  have hz (x : H ⊗[ℚ] filtration 0 0) :
      L (TensorProduct.map (LinearMap.id : H →ₗ[ℚ] H) (filtration 0 0).subtype x) = 0 := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [L, hf b]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  rintro ⟨x, hx⟩
  have hc := congrArg L hx
  rw [hz] at hc
  have hL : L (wordBasis 1 ⊗ₜ[ℚ] wordBasis (FreeMonoid.of 1)) = 1 := by
    simp only [L, TensorProduct.lift.tmul, LinearMap.smulRight_apply,
      LinearMap.smul_apply, pairing_basis, smul_eq_mul]
    change (wordBasis 1).coeff 1 * (wordBasis (FreeMonoid.of 1)).coeff (FreeMonoid.of 1) = 1
    simp [wordBasis]
  rw [hL] at hc
  exact zero_ne_one hc

def filtrationResultArena : Arena where
  signature := transposeSignature
  Law R := ∀ (k r : ℕ) (P : H), P ∈ filtration k r → R.readout () () P ∈ rightFiltrationImage k r

private theorem filtrationResult_rejected : ¬ filtrationResultArena.Law filtrationRejected := by
  intro h
  have hc := h 0 0 0 (Submodule.zero_mem _)
  exact forbidden_tensor hc

def filtrationResultFamily : Registration filtrationResultArena (claim) where
  actual := transposeActual
  bridge := Iff.rfl
  variation := ⟨result, filtrationRejected, filtrationResult_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ filtrationResult_rejected
  dependence := by
    change ObservationalDependence transposeSignature transposeActual
    intro i
    refine ⟨(), (0 : H), wordBasis (1 : Word), ?_⟩
    change delta 0 ≠ delta (wordBasis 1)
    intro he
    have hc := congrArg (fun T : H ⊗[ℚ] H => tensorBasis.repr T (1, 1)) he
    simp only [map_zero, Finsupp.zero_apply] at hc
    rw [delta_basis_coefficient, starWord_one_one] at hc
    simp [wordBasis] at hc

def filtrationResultAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriCoproductFiltration.result) (Realization transposeSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.filtrationResultUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.filtrationResultFamily
  realizationSource := none
  generated := false
  arena := .source ⟨filtrationResultArena⟩
  objectArena := .source ⟨filtrationResultArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source filtrationResultArena ⟨filtrationResultFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transposeSignature (fun _ _ P => delta P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriCoproductFiltration
    definition := some { owner := `D5.S1.Words.PostLie.AriCoproductFiltration, name := `D5.S1.Words.PostLie.AriCoproductFiltration.claim, path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev coefficientSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature H (fun _ => Word) (fun _ => ℚ)
def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ P w => P.coeff w) (fun e => nomatch e)
def coefficientRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 1) (fun e => nomatch e)

def pairingBasisArena : Arena where
  signature := coefficientSignature
  Law R := ∀ (w : Word) (P : H), pairing (wordBasis w) P = R.readout () P w

private theorem pairingBasis_rejected : ¬ pairingBasisArena.Law coefficientRejected := by
  intro h
  have hc := h 1 0
  change pairing (wordBasis 1) 0 = 1 at hc
  rw [map_zero] at hc
  exact zero_ne_one hc

def pairingBasisFamily : Registration pairingBasisArena (∀ (w : Word) (P : H), pairing (wordBasis w) P = P.coeff w) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨pairing_basis, coefficientRejected, pairingBasis_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ pairingBasis_rejected
  dependence := by
    change ObservationalDependence coefficientSignature coefficientActual
    intro i
    refine ⟨wordBasis (1 : Word), (1 : Word), FreeMonoid.of 0, ?_⟩
    change (wordBasis 1).coeff 1 ≠ (wordBasis 1).coeff (FreeMonoid.of 0)
    simp [wordBasis]

def pairingBasisAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.PostLie.AriCoproductFiltration.pairing_basis) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.pairingBasisUnit
  realizationName := `Reg.D5.S1.Words.PostLie.AriCoproductFiltration.pairingBasisFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pairingBasisArena⟩
  objectArena := .source ⟨pairingBasisArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairingBasisArena ⟨pairingBasisFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature (fun _ P w => P.coeff w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.PostLie.AriCoproductFiltration
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.PostLie.AriCoproductFiltration
