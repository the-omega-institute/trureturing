import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

namespace Reg.D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction

open _root_.D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction
open _root_.D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators

noncomputable section

/- The source family retains every finite dimension, real matrix, support and occupation.
The sourceSelection and escapeFrom fields remain unspecified in the contract below.
This is an unfinished escape registration: https://github.com/the-omega-institute/trureturing/issues/29093
-/

abbrev selectionSignature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n) (Fin n) ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def selectionActual : Realization selectionSignature :=
  realize selectionSignature (fun _ _ A => A) (fun e => nomatch e)

abbrev supportArena : Arena where
  signature := selectionSignature
  Law r := ∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}, Aᵀ = -A →
    ∀ {s t : Finset (Fin n)} {w v : Fin n → ℝ},
      _root_.D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.IsSelected
        (r.readout () n A) s w →
      _root_.D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.IsSelected
        (r.readout () n A) t v → s = t

def supportRejected : Realization selectionSignature := by
  classical
  exact realize selectionSignature
    (fun _ _ _ i j => if i = j then 0 else -1) (fun e => nomatch e)

theorem supportRejected_not_law : ¬ supportArena.Law supportRejected := by
  intro h
  have hzero : (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = -0 := by simp
  have hw : _root_.D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.IsSelected
      (supportRejected.readout () 2 0) {0} (![1, 0] : Fin 2 → ℝ) := by
    intro i
    fin_cases i <;> norm_num [supportRejected, realize,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hv : _root_.D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.IsSelected
      (supportRejected.readout () 2 0) {1} (![0, 1] : Fin 2 → ℝ) := by
    intro i
    fin_cases i <;> norm_num [supportRejected, realize,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have he : ({0} : Finset (Fin 2)) = {1} := h hzero hw hv
  have hm : (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) := by rw [← he]; simp
  simpa using hm

def supportSourceRegistration : Registration supportArena
    (∀ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}, Aᵀ = -A →
      ∀ {s t : Finset (Fin n)} {w v : Fin n → ℝ},
        _root_.D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.IsSelected A s w →
        _root_.D5.S3.StatisticalMechanics.BoseSelectionCubicTwoBathRefutation.IsSelected A t v →
        s = t) where
  actual := selectionActual
  bridge := Iff.rfl
  variation := ⟨@selected_support_eq, supportRejected, supportRejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨supportRejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, supportRejected_not_law⟩
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    intro h
    have he := congrFun (congrFun h (0 : Fin 1)) (0 : Fin 1)
    change (0 : ℝ) = 1 at he
    exact zero_ne_one he

def supportRegistrationAttempt :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@selected_support_eq) (Realization selectionSignature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction.supportAttempt
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction.supportSourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportSourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize selectionSignature (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.StatisticalMechanics.BoseSelectionFixedBathConstruction
