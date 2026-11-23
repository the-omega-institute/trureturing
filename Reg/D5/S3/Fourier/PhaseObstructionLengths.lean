import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.PhaseObstructionLengths
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the normalized score, deficit, and omitted weight. -/

namespace Reg.D5.S3.Fourier.PhaseObstructionLengths

open _root_.D5.S3.Fourier.PhaseObstructionLengths
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support
open Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section

universe u v

abbrev System := Σ J : Type u, Σ _ : Finset J, Σ _ : J → ℝ, J → ℝ

abbrev observationSignature (State : Type v) : Signature where
  Params := System.{u}
  State _ := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem singleRoleSensitivity {s : Signature} (law : Realization s → Prop)
    (actual rejected : Realization s) [Subsingleton s.Role] [IsEmpty s.Anchor]
    (h : ¬ law rejected) : Sensitivity ⟨s, law⟩ actual := by
  constructor
  · intro i
    exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
      funext fun e => (IsEmpty.false e).elim, h⟩
  · intro i
    exact (IsEmpty.false i).elim

abbrev timeSignature := observationSignature.{u, 0} ℝ

def timeActual : Realization timeSignature.{u} :=
  realize timeSignature (fun _ p t => average p.2.1 p.2.2.1 p.2.2.2 t) (fun e => nomatch e)

def timeRejected : Realization timeSignature.{u} :=
  realize timeSignature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev timeArena : Arena where
  signature := timeSignature.{u}
  Law r := ∀ {J : Type u} [DecidableEq J] (s : Finset J) (g w : J → ℝ)
    (_hw : ∀ j ∈ s, 0 ≤ w j) (t : ℝ) (N : ℕ),
    let A := r.readout () ⟨J, s, g, w⟩ t
    (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) + perScale s g w (N + 1) ≤ 1 - A

private theorem emptyOmission (J : Type u) [DecidableEq J] (h : ℕ) :
    omissionFraction (∅ : Finset J) (fun _ => 0) (fun _ => 0) h = 0 := by
  obtain ⟨v, _, _, heq⟩ :=
    (omissionFraction_isLeast (∅ : Finset J) (fun _ => 0) (fun _ => 0) h).1
  change _ = (∑ j ∈ (∅ : Finset J) \ v, (0 : ℝ)) / ∑ j ∈ (∅ : Finset J), 0 at heq
  simpa using heq

private theorem timeRejectedLaw : ¬ timeArena.{u}.Law timeRejected := by
  intro law
  let J := ULift.{u} Unit
  have h := law (∅ : Finset J) (fun _ => 0) (fun _ => 0) (by simp) 0 0
  change (∑ n ∈ Finset.Ico 1 (0 + 1),
    summand (∅ : Finset J) (fun _ => 0) (fun _ => 0) n) +
    perScale (∅ : Finset J) (fun _ => 0) (fun _ => 0) 1 ≤ 1 - (2 : ℝ) at h
  norm_num [perScale, emptyOmission J 1] at h

private theorem singletonAverage (t : ℝ) :
    average ({(⟨()⟩ : ULift.{u} Unit)} : Finset (ULift.{u} Unit))
      (fun _ => 1) (fun _ => 1) t = Real.sin t := by
  change (∑ j ∈ ({⟨()⟩} : Finset (ULift.{u} Unit)), (1 : ℝ) * Real.sin (1 * t)) /
    (∑ j ∈ ({⟨()⟩} : Finset (ULift.{u} Unit)), (1 : ℝ)) = Real.sin t
  simp

private theorem timeDependence : ObservationalDependence timeSignature.{u} timeActual := by
  intro _
  let J := ULift.{u} Unit
  let s : Finset J := {⟨()⟩}
  refine ⟨⟨J, s, fun _ => 1, fun _ => 1⟩, 0, Real.pi / 2, ?_⟩
  change average s (fun _ => 1) (fun _ => 1) 0 ≠
    average s (fun _ => 1) (fun _ => 1) (Real.pi / 2)
  rw [show average s (fun _ => 1) (fun _ => 1) = Real.sin from funext singletonAverage]
  simp

def timeSource : Registration timeArena.{u} (type_of% @simultaneous_bound.{u}) where
  actual := timeActual
  bridge := Iff.rfl
  variation := ⟨@simultaneous_bound.{u}, timeRejected, timeRejectedLaw⟩
  sensitivity := singleRoleSensitivity timeArena.{u}.Law timeActual timeRejected timeRejectedLaw
  dependence := timeDependence

def timeAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@simultaneous_bound.{u}) (Realization timeSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.PhaseObstructionLengths.timeUnit
  realizationName := `Reg.D5.S3.Fourier.PhaseObstructionLengths.timeSource
  realizationSource := none
  generated := false
  arena := .source ⟨timeArena.{u}⟩
  objectArena := .source ⟨timeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source timeArena.{u} ⟨timeSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize timeSignature
    (fun _ p t => average p.2.1 p.2.2.1 p.2.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.PhaseObstructionLengths
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev deficitSignature := observationSignature.{u, 0} (Set ℝ)

def deficitActual : Realization deficitSignature.{u} :=
  realize deficitSignature (fun _ p T => deficit p.2.1 p.2.2.1 p.2.2.2 T) (fun e => nomatch e)

def deficitRejected : Realization deficitSignature.{u} :=
  realize deficitSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev deficitArena : Arena where
  signature := deficitSignature.{u}
  Law r := ∀ {J : Type u} [DecidableEq J] (s : Finset J) (g w : J → ℝ) (T : Set ℝ)
    (_hw : ∀ j ∈ s, 0 ≤ w j),
    let D := r.readout () ⟨J, s, g, w⟩ T
    let L := ∑' n, summand s g w (n + 1)
    (∀ N : ℕ, (∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h) +
      perScale s g w (N + 1) ≤ D) ∧
      HasSum (fun n => summand s g w (n + 1)) L ∧
      sSup (perScale s g w '' Set.Ici 1) ≤ L ∧ L ≤ D ∧
      (∀ N : ℕ, let S := ∑ h ∈ Finset.Ico 1 (N + 1), summand s g w h
        perScale s g w (N + 1) ≤ L - S ∧ L - S ≤ 1 / ((N + 1 : ℕ) : ℝ) ^ 2)

private theorem deficitRejectedLaw : ¬ deficitArena.{u}.Law deficitRejected := by
  intro law
  let J := ULift.{u} Unit
  have h := (law (∅ : Finset J) (fun _ => 0) (fun _ => 0) ∅ (by simp)).2.2.2.1
  have hz : ∀ n : ℕ, summand (∅ : Finset J) (fun _ => 0) (fun _ => 0) (n + 1) = 0 := by
    intro n
    simp [summand, emptyOmission J (n + 1)]
  change (∑' n, summand (∅ : Finset J) (fun _ => 0) (fun _ => 0) (n + 1)) ≤ -1 at h
  norm_num [hz] at h

private theorem deficitDependence :
    ObservationalDependence deficitSignature.{u} deficitActual := by
  intro _
  let J := ULift.{u} Unit
  let s : Finset J := {⟨()⟩}
  refine ⟨⟨J, s, fun _ => 1, fun _ => 1⟩, {0}, {Real.pi / 2}, ?_⟩
  change deficit s (fun _ => 1) (fun _ => 1) {0} ≠
    deficit s (fun _ => 1) (fun _ => 1) {Real.pi / 2}
  have h : average s (fun _ => 1) (fun _ => 1) = Real.sin := funext singletonAverage
  simp [deficit, h]

def deficitSource : Registration deficitArena.{u} (type_of% @aggregate_bounds.{u}) where
  actual := deficitActual
  bridge := Iff.rfl
  variation := ⟨@aggregate_bounds.{u}, deficitRejected, deficitRejectedLaw⟩
  sensitivity := singleRoleSensitivity deficitArena.{u}.Law deficitActual deficitRejected
    deficitRejectedLaw
  dependence := deficitDependence

def deficitAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@aggregate_bounds.{u}) (Realization deficitSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.PhaseObstructionLengths.deficitUnit
  realizationName := `Reg.D5.S3.Fourier.PhaseObstructionLengths.deficitSource
  realizationSource := none
  generated := false
  arena := .source ⟨deficitArena.{u}⟩
  objectArena := .source ⟨deficitArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deficitArena.{u} ⟨deficitSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deficitSignature
    (fun _ p T => deficit p.2.1 p.2.2.1 p.2.2.2 T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.PhaseObstructionLengths
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev omissionSignature : Signature where
  Params := Σ J : Type u, Σ _ : DecidableEq J, Σ _ : Finset J, Σ _ : J → ℝ, J → ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def omissionActual : Realization omissionSignature.{u} :=
  realize omissionSignature (fun _ p h =>
    @omissionFraction p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 h) (fun e => nomatch e)

def omissionRejected : Realization omissionSignature.{u} :=
  realize omissionSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev omissionArena : Arena where
  signature := omissionSignature.{u}
  Law r := ∀ {J : Type u} [inst : DecidableEq J] (s : Finset J) (g w : J → ℝ) (h : ℕ),
    let P := r.readout () ⟨J, inst, s, g, w⟩ h
    IsLeast {p | ∃ u ⊆ s, (∀ k : J → ℤ, (∀ j ∉ u, k j = 0) →
      (∑ j ∈ s, (k j : ℝ) * g j) = 0 →
      (∑ j ∈ s, |k j|) ≤ (h : ℤ) → (4 : ℤ) ∣ ∑ j ∈ s, k j) ∧
      p = (∑ j ∈ s \ u, w j) / (∑ j ∈ s, w j)} P

private theorem omissionRejectedLaw : ¬ omissionArena.{u}.Law omissionRejected := by
  intro law
  let J := ULift.{u} Unit
  obtain ⟨v, hv, _, heq⟩ := (law (∅ : Finset J) (fun _ => 0) (fun _ => 0) 1).1
  change (-1 : ℝ) = (∑ j ∈ (∅ : Finset J) \ v, (0 : ℝ)) / ∑ j ∈ (∅ : Finset J), 0 at heq
  norm_num at heq

private theorem omissionDependence :
    ObservationalDependence omissionSignature.{u} omissionActual := by
  intro _
  let J := ULift.{u} Unit
  let s : Finset J := {⟨()⟩}
  let g : J → ℝ := fun _ => 0
  let w : J → ℝ := fun _ => 1
  refine ⟨⟨J, inferInstance, s, g, w⟩, 0, 1, ?_⟩
  change omissionFraction s g w 0 ≠ omissionFraction s g w 1
  have h₀ : IsLeast _ (omissionFraction s g w 0) :=
    omissionFraction_isLeast s g w 0
  have h₁ : IsLeast _ (omissionFraction s g w 1) :=
    omissionFraction_isLeast s g w 1
  have hp₀ := h₀.2 (show (0 : ℝ) ∈ _ from
    ⟨s, Subset.rfl, by
      intro k _ _ hn
      have hk : k ⟨()⟩ = 0 := by
        simp only [s, Finset.sum_singleton, Nat.cast_zero] at hn
        exact abs_nonpos_iff.mp hn
      simp [s, hk], by
        change (0 : ℝ) = (∑ j ∈ s \ s, w j) / ∑ j ∈ s, w j
        simp⟩)
  obtain ⟨v, hv, hgood, heq⟩ := h₁.1
  have hv₀ : v = ∅ := by
    rcases Finset.subset_singleton_iff.mp hv with he | he
    · exact he
    · subst v
      have hsupp (j : J) (hj : j ∉ ({⟨()⟩} : Finset J)) : (1 : ℤ) = 0 := by
        exact (hj (by simp [Subsingleton.elim j ⟨()⟩])).elim
      have hbad := hgood (fun _ => 1) hsupp (by simp [s, g]) (by simp [s])
      norm_num [s] at hbad
  have hp₁ : omissionFraction s g w 1 = 1 := by
    change omissionFraction s g w 1 = (∑ j ∈ s \ v, w j) / ∑ j ∈ s, w j at heq
    simpa [hv₀, w, s] using heq
  linarith only [hp₀, hp₁]

def omissionSource : Registration omissionArena.{u} (type_of% @omissionFraction_isLeast.{u}) where
  actual := omissionActual
  bridge := Iff.rfl
  variation := ⟨@omissionFraction_isLeast.{u}, omissionRejected, omissionRejectedLaw⟩
  sensitivity := singleRoleSensitivity omissionArena.{u}.Law omissionActual omissionRejected
    omissionRejectedLaw
  dependence := omissionDependence

def omissionAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@omissionFraction_isLeast.{u}) (Realization omissionSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.PhaseObstructionLengths.omissionUnit
  realizationName := `Reg.D5.S3.Fourier.PhaseObstructionLengths.omissionSource
  realizationSource := none
  generated := false
  arena := .source ⟨omissionArena.{u}⟩
  objectArena := .source ⟨omissionArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source omissionArena.{u} ⟨omissionSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize omissionSignature
    (fun _ p h => @omissionFraction p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.PhaseObstructionLengths
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev exampleSignature := SingleDependentReadout.signature Unit (fun _ => Fin 3) (fun _ => ℝ)

def exampleActual : Realization exampleSignature :=
  realize exampleSignature (fun _ _ j => exampleFreq j) (fun e => nomatch e)

def exampleRejected : Realization exampleSignature :=
  realize exampleSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev exampleArena : Arena where
  signature := exampleSignature
  Law r :=
    let g := fun j => r.readout () () j
    (omissionFraction Finset.univ g exampleWeight 1 = 1 / 2 ∧
      omissionFraction Finset.univ g exampleWeight 2 = 1 / 2 ∧
      (∀ h : ℕ, 3 ≤ h → omissionFraction Finset.univ g exampleWeight h = 3 / 4)) ∧
    let B := sSup (perScale Finset.univ g exampleWeight '' Set.Ici 1)
    let S (N : ℕ) := ∑ h ∈ Finset.Ico 1 (N + 1), summand Finset.univ g exampleWeight h
    B = 1 / 2 ∧ S 5 = 73 / 144 ∧ B < S 5 ∧
      (∑' n, summand Finset.univ g exampleWeight (n + 1)) = 19 / 36 ∧
      (∀ N : ℕ, 2 ≤ N → S N = 19 / 36 - 3 / (4 * ((N + 1 : ℕ) : ℝ) ^ 2)) ∧
      IsLeast {N : ℕ | B < S N} 5

private theorem exampleRejectedLaw : ¬ exampleArena.Law exampleRejected := by
  intro law
  have h := omissionFraction_isLeast Finset.univ (fun _ => 1) exampleWeight 1
  have hP := h.2 (show (0 : ℝ) ∈ _ from
    ⟨Finset.univ, Subset.rfl, by
      intro k _ hk _
      simp only [mul_one, ← Int.cast_sum] at hk
      have hz : ∑ j : Fin 3, k j = 0 := by exact_mod_cast hk
      rw [hz]
      exact dvd_zero _, by
        change (0 : ℝ) = (∑ j ∈ (Finset.univ : Finset (Fin 3)) \ Finset.univ,
          exampleWeight j) / ∑ j, exampleWeight j
        simp⟩)
  have hp : omissionFraction Finset.univ (fun _ => 1) exampleWeight 1 = 1 / 2 := law.1.1
  linarith only [hp, hP]

private theorem exampleDependence : ObservationalDependence exampleSignature exampleActual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change exampleFreq 0 ≠ exampleFreq 1
  norm_num [exampleFreq]

def exampleSource : Registration exampleArena (type_of% @strict_three_frequency_example) where
  actual := exampleActual
  bridge := Iff.rfl
  variation := ⟨strict_three_frequency_example, exampleRejected, exampleRejectedLaw⟩
  sensitivity := SingleDependentReadout.sensitivity exampleArena.Law exampleActual exampleRejected
    exampleRejectedLaw
  dependence := exampleDependence

def exampleAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@strict_three_frequency_example) (Realization exampleSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.PhaseObstructionLengths.exampleUnit
  realizationName := `Reg.D5.S3.Fourier.PhaseObstructionLengths.exampleSource
  realizationSource := none
  generated := false
  arena := .source ⟨exampleArena⟩
  objectArena := .source ⟨exampleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exampleArena ⟨exampleSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize exampleSignature (fun _ _ j => exampleFreq j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.PhaseObstructionLengths
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.PhaseObstructionLengths
