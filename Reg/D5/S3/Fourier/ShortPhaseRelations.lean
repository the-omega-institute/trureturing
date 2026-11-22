import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.ShortPhaseRelations
import Reg.Support.DependentFamily

/-! The observations are the weighted deficits as functions of the real time domain. -/

namespace Reg.D5.S3.Fourier.ShortPhaseRelations

open _root_.D5.S3.Fourier.ShortPhaseRelations
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section

universe u

private theorem singletonTime_deficit (n : Type u) (s : Finset n) (g w : n → ℝ) (t : ℝ) :
    weightedDeficit s g w {t} =
      1 - (∑ j ∈ s, w j * Real.sin (g j * t)) / ∑ j ∈ s, w j := by
  simp [weightedDeficit]
  rfl

private theorem singleRoleSensitivity {s : Signature} (law : Realization s → Prop)
    (actual rejected : Realization s) [Subsingleton s.Role] [IsEmpty s.Anchor]
    (h : ¬ law rejected) : Sensitivity ⟨s, law⟩ actual := by
  constructor
  · intro i
    exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
      funext fun e => (IsEmpty.false e).elim, h⟩
  · intro i
    exact (IsEmpty.false i).elim

abbrev weightedSignature : Signature where
  Params := Σ J : Type u, Σ _ : Finset J, Σ _ : J → ℝ, J → ℝ
  State _ := Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightedActual : Realization weightedSignature.{u} :=
  realize weightedSignature (fun _ p T => weightedDeficit p.2.1 p.2.2.1 p.2.2.2 T)
    (fun e => nomatch e)

def weightedRejected : Realization weightedSignature.{u} :=
  realize weightedSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev weightedArena : Arena where
  signature := weightedSignature.{u}
  Law r := ∀ {J : Type u} [DecidableEq J] (s : Finset J) (g w : J → ℝ)
    (H : ℝ) (T : Set ℝ) (_hs : s.Nonempty) (_hw : ∀ j ∈ s, 0 < w j) (_hH : 1 ≤ H)
    (_hshort : HasShortIncompatibleRelations s g H) (_htail : ∃ a, Ici a ⊆ T),
    let P := deletionFraction s g w
    let D := r.readout () ⟨J, s, g, w⟩ T
    P / (2 * H ^ 2) ≤ D ∧ D ≤ 2 * P ∧ P / H ^ 2 ≤ D

private theorem weightedRejectedLaw : ¬ weightedArena.{u}.Law weightedRejected := by
  classical
  let J := ULift.{u} Unit
  let s : Finset J := {⟨()⟩}
  let g : J → ℝ := fun _ => 1
  let w : J → ℝ := fun _ => 1
  have hshort : HasShortIncompatibleRelations s g 1 := by
    intro v hvs hbad
    exfalso
    apply hbad
    intro k h
    rcases Finset.subset_singleton_iff.mp hvs with rfl | rfl
    · simp
    · have hz : k (⟨()⟩ : J) = 0 := by
        simp only [Finset.sum_singleton, g, mul_one] at h
        exact_mod_cast h
      simp [hz]
  have hP : 0 ≤ deletionFraction s g w := by
    unfold deletionFraction
    apply le_csInf
    · exact ⟨_, ∅, Finset.empty_subset _, by intro k _; simp, rfl⟩
    · rintro _ ⟨v, _, _, rfl⟩
      exact div_nonneg (Finset.sum_nonneg fun _ _ => zero_le_one)
        (Finset.sum_nonneg fun _ _ => zero_le_one)
  intro law
  have h := (law s g w 1 univ (Finset.singleton_nonempty _) (fun _ _ => zero_lt_one)
    le_rfl hshort ⟨0, subset_univ _⟩).2.2
  change deletionFraction s g w / (1 : ℝ) ^ 2 ≤ -1 at h
  norm_num at h
  linarith only [hP, h]

private theorem weightedDependence :
    ObservationalDependence weightedSignature.{u} weightedActual := by
  intro _
  let J := ULift.{u} Unit
  let s : Finset J := {⟨()⟩}
  refine ⟨⟨J, s, fun _ => 1, fun _ => 1⟩, {0}, {Real.pi / 2}, ?_⟩
  change weightedDeficit s (fun _ => 1) (fun _ => 1) {0} ≠
    weightedDeficit s (fun _ => 1) (fun _ => 1) {Real.pi / 2}
  simp [singletonTime_deficit, s]

def weightedSource :
    Registration weightedArena.{u} (type_of% @weighted_deletion_bounds.{u}) where
  actual := weightedActual
  bridge := Iff.rfl
  variation := ⟨@weighted_deletion_bounds.{u}, weightedRejected, weightedRejectedLaw⟩
  sensitivity := singleRoleSensitivity weightedArena.{u}.Law weightedActual weightedRejected
    weightedRejectedLaw
  dependence := weightedDependence

def weightedAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_deletion_bounds.{u}) (Realization weightedSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ShortPhaseRelations.weightedUnit
  realizationName := `Reg.D5.S3.Fourier.ShortPhaseRelations.weightedSource
  realizationSource := none
  generated := false
  arena := .source ⟨weightedArena.{u}⟩
  objectArena := .source ⟨weightedArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightedArena.{u} ⟨weightedSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightedSignature
    (fun _ p T => weightedDeficit p.2.1 p.2.2.1 p.2.2.2 T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ShortPhaseRelations
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev pairSignature : Signature where
  Params := Σ _ : ℕ, ℝ
  State _ := Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def pairActual : Realization pairSignature :=
  realize pairSignature (fun _ p T => weightedDeficit Finset.univ (pairFreq p.1)
    (fun _ => p.2) T) (fun e => nomatch e)

def pairRejected : Realization pairSignature :=
  realize pairSignature (fun _ _ _ => Real.pi ^ 2 + 1) (fun e => nomatch e)

abbrev pairArena : Arena where
  signature := pairSignature
  Law r := ∀ (n : ℕ) (w : ℝ) (_hn : 0 < n) (_hw : 0 < w) (T : Set ℝ)
    (_htail : ∃ a, Ici a ⊆ T),
    let H := 2 * (n : ℝ) + 1
    let g := pairFreq n
    let D := r.readout () ⟨n, w⟩ T
    deletionFraction Finset.univ g (fun _ => w) = 1 / 2 ∧
      HasShortIncompatibleRelations Finset.univ g H ∧
      1 / (4 * H ^ 2) ≤ D ∧ D ≤ (Real.pi ^ 2 / 8) / H ^ 2 ∧
      1 / (2 * H ^ 2) ≤ D

private theorem pairRejectedLaw : ¬ pairArena.Law pairRejected := by
  intro law
  have h := (law 1 1 Nat.one_pos zero_lt_one univ ⟨0, subset_univ _⟩).2.2.2.1
  change Real.pi ^ 2 + 1 ≤ (Real.pi ^ 2 / 8) / (2 * ((1 : ℕ) : ℝ) + 1) ^ 2 at h
  norm_num at h
  nlinarith only [h, sq_nonneg Real.pi]

private theorem pairDependence : ObservationalDependence pairSignature pairActual := by
  intro _
  refine ⟨⟨1, 1⟩, {0}, {Real.pi / 4}, ?_⟩
  change weightedDeficit Finset.univ (pairFreq 1) (fun _ => 1) {0} ≠
    weightedDeficit Finset.univ (pairFreq 1) (fun _ => 1) {Real.pi / 4}
  rw [singletonTime_deficit, singletonTime_deficit]
  have h : (1 + 1 : ℝ) * (Real.pi / 4) = Real.pi / 2 := by ring
  have hp : 0 < Real.sin (Real.pi / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith only [Real.pi_pos])
  simp only [Fin.sum_univ_two, pairFreq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.cast_one, mul_zero, Real.sin_zero, mul_one, one_mul, add_zero, sub_zero,
    zero_div, h, Real.sin_pi_div_two]
  linarith only [hp]

def pairSource : Registration pairArena (type_of% @consecutive_pair_separation) where
  actual := pairActual
  bridge := Iff.rfl
  variation := ⟨@consecutive_pair_separation, pairRejected, pairRejectedLaw⟩
  sensitivity := singleRoleSensitivity pairArena.Law pairActual pairRejected pairRejectedLaw
  dependence := pairDependence

def pairAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@consecutive_pair_separation) (Realization pairSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.ShortPhaseRelations.pairUnit
  realizationName := `Reg.D5.S3.Fourier.ShortPhaseRelations.pairSource
  realizationSource := none
  generated := false
  arena := .source ⟨pairArena⟩
  objectArena := .source ⟨pairArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairArena ⟨pairSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ p T =>
    weightedDeficit Finset.univ (pairFreq p.1) (fun _ => p.2) T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.ShortPhaseRelations
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.ShortPhaseRelations
