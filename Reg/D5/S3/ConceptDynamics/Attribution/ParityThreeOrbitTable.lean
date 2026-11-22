import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable
import Reg.Support.DependentFamily

/-! Dependence of orbit table feasibility on the prescribed fixed counts. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedBudget
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
open _root_.D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := Fin 3 → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ k z => Nonempty (OrbitTable k z)) (fun e => nomatch e)

def unrestricted : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k (z : Fin 3 → ℕ), RealizableSeedCounts 1 k z ↔ R.readout () k z

private theorem no_fixed_at_zero : ¬ RealizableSeedCounts 1 0 (fun _ => 1) := by
  rintro ⟨S, _, _, _, card, _, _, fixed⟩
  have empty : IsEmpty S := Fintype.card_eq_zero_iff.mp (by simpa using card)
  have h := fixed 0
  simp [fixedSeedCount] at h

private theorem unrestricted_fails : ¬ arena.Law unrestricted := by
  intro law
  exact no_fixed_at_zero ((law 0 (fun _ => 1)).mpr True.intro)

def family : Registration arena (type_of% exact_orbit_table) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_orbit_table, unrestricted, unrestricted_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨unrestricted, ?_, rfl, unrestricted_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    refine ⟨0, fun _ => 0, fun _ => 1, ?_⟩
    change Nonempty (OrbitTable 0 (fun _ => 0)) ≠ Nonempty (OrbitTable 0 (fun _ => 1))
    intro same
    have zero : RealizableSeedCounts 1 0 (fun _ => 0) :=
      (zero_coordinate_counts_iff 1 0).mpr (Or.inr ⟨0, rfl⟩)
    exact no_fixed_at_zero ((exact_orbit_table 0 _).mpr (same ▸ (exact_orbit_table 0 _).mp zero))

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_orbit_table (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable.feasibility
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k z => Nonempty (OrbitTable k z)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev profileSignature : Signature where
  Params := Unit
  State _ := Fin 4
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ParityClass 3 0
  Anchor := Empty
  finiteAnchor := inferInstance

def profiles : Realization profileSignature :=
  realize profileSignature (fun _ _ => leftProfile) (fun e => nomatch e)

def constantProfile : Realization profileSignature :=
  realize profileSignature (fun _ _ _ => leftProfile 0) (fun e => nomatch e)

abbrev profileArena : Arena where
  signature := profileSignature
  Law R := Function.Bijective (fun p => R.readout () () p)

private theorem constant_profile_fails : ¬ profileArena.Law constantProfile := by
  intro law
  exact (by decide : (0 : Fin 4) ≠ 1) (law.injective (show leftProfile 0 = leftProfile 0 from rfl))

def profileFamily : Registration profileArena (type_of% leftProfile_bijective) where
  actual := profiles
  bridge := Iff.rfl
  variation := ⟨leftProfile_bijective, constantProfile, constant_profile_fails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨constantProfile, ?_, rfl, constant_profile_fails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · exact fun e => nomatch e
  dependence := by
    rintro ⟨⟩
    refine ⟨(), 0, 1, ?_⟩
    exact fun eq => (by decide : (0 : Fin 4) ≠ 1) (leftProfile_bijective.injective eq)

def profileRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    leftProfile_bijective (Realization profileSignature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable.profileIndex
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable.profileFamily
  realizationSource := none
  generated := false
  arena := .source ⟨profileArena⟩
  objectArena := .source ⟨profileArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source profileArena ⟨profileFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize profileSignature (fun _ _ => leftProfile) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParityThreeOrbitTable
