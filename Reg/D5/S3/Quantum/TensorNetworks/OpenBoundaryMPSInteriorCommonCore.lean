import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
import Reg.Support.DependentFamily

/-! Source-faithful dependent-family audits. The finite target certificate tests
inhabited hypotheses; it supplies no additional source theorem. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore

open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality (mpsState)
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Matrix ComplexOrder
set_option autoImplicit false
noncomputable section

private def certificateCore : Fin 2 → Bond :=
  ![!![1, 0; 0, 2], !![0, 1; 1, 0]]

private lemma certificate_spanning : TwoSiteSpanning certificateCore := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro M
  let S := Submodule.span ℂ
    (Set.range fun p : Fin 2 × Fin 2 => certificateCore p.1 * certificateCore p.2)
  have hp (i j : Fin 2) : certificateCore i * certificateCore j ∈ S :=
    Submodule.subset_span ⟨(i, j), rfl⟩
  have hm := S.add_mem
    (S.add_mem
      (S.smul_mem ((M 1 1 - M 0 0) / 3) (hp 0 0))
      (S.smul_mem ((4 * M 0 0 - M 1 1) / 3) (hp 1 1)))
    (S.add_mem
      (S.smul_mem ((2 * M 1 0 - M 0 1) / 3) (hp 0 1))
      (S.smul_mem ((2 * M 0 1 - M 1 0) / 3) (hp 1 0)))
  convert hm using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [certificateCore, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

private lemma certificate_left :
    ((dualTransfer certificateCore)^[1]
      (vecMulVec (star (![1, 0] : Fin 2 → ℂ)) ![1, 0])).PosDef := by
  have he : (dualTransfer certificateCore)^[1]
      (vecMulVec (star (![1, 0] : Fin 2 → ℂ)) ![1, 0]) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dualTransfer, certificateCore, mul_apply, Fin.sum_univ_two]
  rw [he]
  exact Matrix.PosDef.one

private lemma certificate_right :
    ((transfer certificateCore)^[1]
      (vecMulVec (![1, 0] : Fin 2 → ℂ) (star ![1, 0]))).PosDef := by
  have he : (transfer certificateCore)^[1]
      (vecMulVec (![1, 0] : Fin 2 → ℂ) (star ![1, 0])) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [transfer, certificateCore, mul_apply, Fin.sum_univ_two,
        vecMulVec, Pi.star_def, Matrix.vecMul, dotProduct,
        Matrix.vecHead, Matrix.vecTail, Matrix.conjTranspose_apply]
  rw [he]
  exact Matrix.PosDef.one

namespace AllCoefficients

abbrev signature : Signature where
  Params := ℕ
  State m := Word (m + 3) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := (Word (m + 3) → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f g => f = g) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A B : Fin 2 → Bond), TwoSiteSpanning A →
    (∀ X : Bond, ∃ Y : Bond, gamma B 3 X = gamma A 3 Y) →
    ∀ (m : ℕ) (X : Bond), ∃ Y : Bond,
      R.readout () m (gamma B (m + 3) X) (gamma A (m + 3) Y)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hf⟩ := h certificateCore certificateCore certificate_spanning
    (fun X => ⟨X, rfl⟩) 0 0
  exact hf

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro h
  have he : (1 : Word 3 → ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  have hv := congrFun he (fun _ => 0)
  norm_num at hv

def source_registration : Registration arena (type_of% @all_coefficient_parent_induction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@all_coefficient_parent_induction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@all_coefficient_parent_induction) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.all_coefficient_parent_induction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.AllCoefficients.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f g => f = g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end AllCoefficients

namespace CommonCore

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State pq := Word ((pq.1 + 3) + pq.2) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ pq := (Word ((pq.1 + 3) + pq.2) → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f g => f = g) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A B : Fin 2 → Bond) (l r lprime rprime : Fin 2 → ℂ)
    (p q : ℕ), 1 ≤ p → 1 ≤ q → TwoSiteSpanning A →
    ((dualTransfer A)^[p] (vecMulVec (star l) l)).PosDef →
    ((transfer A)^[q] (vecMulVec r (star r))).PosDef →
    rawInterior p 3 q (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime) =
      rawInterior p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r) →
    ∃ X : Bond, R.readout () ⟨p, q⟩
      (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime) (gamma A ((p + 3) + q) X)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hf⟩ := h certificateCore certificateCore ![1, 0] ![1, 0] ![1, 0] ![1, 0]
    1 1 (by omega) (by omega) certificate_spanning certificate_left certificate_right rfl
  exact hf

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  intro h
  have he : (1 : Word 5 → ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  have hv := congrFun he (fun _ => 0)
  norm_num at hv

def source_registration : Registration arena (type_of% @interior_common_core) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_common_core, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@interior_common_core) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.interior_common_core.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.CommonCore.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f g => f = g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
    definition := none
    coordinates := #[6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CommonCore

namespace RankOne

abbrev signature : Signature where
  Params := Bond × ℕ
  State p := Word p.2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Word p.2 → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f g => f = g) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A B : Fin 2 → Bond) (lprime rprime : Fin 2 → ℂ)
    (N : ℕ), 4 ≤ N → TwoSiteSpanning A → ∀ X : Bond,
    mpsState N (B 0) (B 1) lprime rprime = gamma A N X →
    X.rank ≤ 1 ∧ ∃ lA rA : Fin 2 → ℂ,
      X = vecMulVec rA lA ∧
      R.readout () (X, N)
        (mpsState N (B 0) (B 1) lprime rprime)
        (mpsState N (A 0) (A 1) lA rA)

private lemma zero_common_core :
    mpsState 4 (certificateCore 0) (certificateCore 1)
        (![0, 0] : Fin 2 → ℂ) (![0, 0] : Fin 2 → ℂ) =
      gamma certificateCore 4 0 := by
  funext w
  rw [state_formula, gamma]
  simp [vecMulVec, Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hf⟩ := h certificateCore certificateCore ![0, 0] ![0, 0] 4
    (by omega) certificate_spanning 0 zero_common_core
  obtain ⟨lA, rA, _, hf⟩ := hf
  exact hf

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, 4), 0, 1, ?_⟩
  intro h
  have he : (1 : Word 4 → ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  have hv := congrFun he (fun _ => 0)
  norm_num at hv

def source_registration : Registration arena (type_of% @common_core_rank_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@common_core_rank_one, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@common_core_rank_one) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.common_core_rank_one.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.RankOne.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f g => f = g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
    definition := none
    coordinates := #[8]
    readouts := #[{
      path := #[],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RankOne

namespace Phase

private lemma certificate_transfer : Function.Injective (transfer certificateCore) := by
  intro X Y h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  norm_num [transfer, certificateCore, mul_apply, Matrix.vecMul, dotProduct,
    conjTranspose_apply, Fin.sum_univ_two, map_ofNat] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · change X 0 0 = Y 0 0
    linear_combination (4 / 3 : ℂ) * h00 - (1 / 3 : ℂ) * h11
  · change X 0 1 = Y 0 1
    linear_combination (2 / 3 : ℂ) * h01 - (1 / 3 : ℂ) * h10
  · change X 1 0 = Y 1 0
    linear_combination (2 / 3 : ℂ) * h10 - (1 / 3 : ℂ) * h01
  · change X 1 1 = Y 1 1
    linear_combination (1 / 3 : ℂ) * h11 - (1 / 3 : ℂ) * h00

private def target : Word 5 → ℂ :=
  mpsState 5 (certificateCore 0) (certificateCore 1) ![1, 0] ![1, 0]

private def competitor : Word 5 → ℂ :=
  mpsState 5 (certificateCore 0) (certificateCore 1)
    (Complex.I • (![1, 0] : Fin 2 → ℂ)) ![1, 0]

private lemma complex_state : competitor = Complex.I • target := by
  funext w
  simp [competitor, target, mpsState]

private lemma complex_raw : rawInterior 1 3 1 competitor = rawInterior 1 3 1 target := by
  rw [complex_state]
  have hc : interiorColumns 1 3 1 (Complex.I • target) =
      Complex.I • interiorColumns 1 3 1 target := rfl
  simp only [rawInterior, hc, conjTranspose_smul, Matrix.mul_smul]
  simp [smul_smul]

private lemma complex_nonzero : competitor ≠ 0 := by
  intro h
  have he := congrFun h (fun _ => 0)
  norm_num [competitor, mpsState, certificateCore, List.ofFn_succ,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at he

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State pq := Word ((pq.1 + 3) + pq.2) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ pq := (Word ((pq.1 + 3) + pq.2) → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f g => f = g) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ f _ => f = 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A B : Fin 2 → Bond) (l r lprime rprime : Fin 2 → ℂ)
    (p q : ℕ), 1 ≤ p → 1 ≤ q → TwoSiteSpanning A →
    Function.Injective (transfer A) →
    ((dualTransfer A)^[p] (vecMulVec (star l) l)).PosDef →
    ((transfer A)^[q] (vecMulVec r (star r))).PosDef →
    rawInterior p 3 q (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime) =
      rawInterior p 3 q (mpsState ((p + 3) + q) (A 0) (A 1) l r) →
    ∃ z : ℂ, ‖z‖ = 1 ∧ R.readout () ⟨p, q⟩
      (mpsState ((p + 3) + q) (B 0) (B 1) lprime rprime)
      (z • mpsState ((p + 3) + q) (A 0) (A 1) l r)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, hf⟩ := h certificateCore certificateCore ![1, 0] ![1, 0]
    (Complex.I • (![1, 0] : Fin 2 → ℂ)) ![1, 0] 1 1 (by omega) (by omega)
    certificate_spanning certificate_transfer certificate_left certificate_right complex_raw
  exact complex_nonzero hf

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  intro h
  have he : (1 : Word 5 → ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  have hv := congrFun he (fun _ => 0)
  norm_num at hv

def source_registration : Registration arena (type_of% @interior_phase_recovery) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_phase_recovery, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@interior_phase_recovery) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.interior_phase_recovery.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore.Phase.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f g => f = g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
    definition := none
    coordinates := #[6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Phase

#print axioms AllCoefficients.registration
#print axioms CommonCore.registration
#print axioms RankOne.registration
#print axioms Phase.registration

end
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
