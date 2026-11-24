import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.SteinerSwitchCentre

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered)
open PointDeletedSteinerSwitch (pointDeletedFamily)
open SteinerAlternatingSwitches (SuccessfulStart point_deleted_successful_starts)
open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre

noncomputable section

private def affineLine : Fin 12 → Finset (Fin 9) :=
  ![{0, 1, 2}, {3, 4, 5}, {6, 7, 8},
    {0, 3, 6}, {1, 4, 7}, {2, 5, 8},
    {0, 4, 8}, {1, 5, 6}, {2, 3, 7},
    {0, 5, 7}, {1, 3, 8}, {2, 4, 6}]

private def affinePlane : Set (Set (Fin 9)) :=
  Set.range (fun i => (affineLine i : Set (Fin 9)))

theorem affinePlane_valid : IsPartialSteiner affinePlane := by
  have card : ∀ i, (affineLine i).card = 3 := by decide
  have unique : ∀ (i j : Fin 12) (x y : Fin 9), x ≠ y →
      x ∈ affineLine i → y ∈ affineLine i → x ∈ affineLine j → y ∈ affineLine j → i = j := by
    decide
  constructor
  · rintro s ⟨i, rfl⟩
    simpa using card i
  · rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ x y ne hxi hyi hxj hyj
    rw [unique i j x y ne hxi hyi hxj hyj]

theorem affinePlane_complete : ∀ a b, a ≠ b → Covered affinePlane a b := by
  have pair : ∀ a b, a ≠ b → ∃ i, a ∈ affineLine i ∧ b ∈ affineLine i := by decide
  intro a b ne
  obtain ⟨i, ha, hb⟩ := pair a b ne
  exact ⟨affineLine i, ⟨i, rfl⟩, ha, hb⟩


theorem affine_noncentral :
    ¬ @IsMulCentral _ (steinerMul affinePlane_valid affinePlane_complete) (some (0 : Fin 9)) := by
  apply (admits_switch_iff_not_central affinePlane_valid affinePlane_complete 0).mp
  obtain ⟨_, m, leave, hp⟩ := point_deleted_successful_starts affinePlane
    affinePlane_valid affinePlane_complete (0 : Fin 9)
  let good : Set (Fin 8) := {a | SuccessfulStart (pointDeletedFamily affinePlane 0) m 0 a}
  have size : 6 ≤ good.ncard := (hp 0).2.2 (by decide)
  have ne : good.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, Set.ncard_empty] at size
    omega
  obtain ⟨a, ha⟩ := ne
  exact ⟨m, leave, 0, a, ha⟩


private theorem empty_not_admitted {r : ℕ} (q : Fin (r + 1)) :
    ¬ AdmitsSwitch ∅ q := by
  rintro ⟨m, leave, v, a, hva, hvma, b, d, hb, hd, ne⟩
  exact hb

abbrev sig :=
  signature ℕ (fun r => Set (Set (Fin (r + 1)))) (fun r => Fin (r + 1) → Prop)

def actual : Realization sig :=
  realize sig (fun _ _ S => AdmitsSwitch S) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ _ => False) (fun e => nomatch e)

def equivalenceLaw (R : Realization sig) : Prop :=
  ∀ {r : ℕ} {S : Set (Set (Fin (r + 1)))}
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)
    (q : Fin (r + 1)),
    R.readout () r S q ↔ ¬ @IsMulCentral _ (steinerMul valid complete) (some q)

abbrev equivalenceArena : Arena := ⟨sig, equivalenceLaw⟩

private theorem equivalence_rejected : ¬ equivalenceLaw rejected := by
  intro h
  exact (h affinePlane_valid affinePlane_complete 0).mpr affine_noncentral

private theorem dependence : ObservationalDependence sig actual := by
  intro i
  refine ⟨8, affinePlane, ∅, ?_⟩
  intro eq
  have same : AdmitsSwitch affinePlane 0 = AdmitsSwitch ∅ 0 := congrFun eq 0
  have hasSwitch := (admits_switch_iff_not_central affinePlane_valid affinePlane_complete 0).mpr
    affine_noncentral
  exact empty_not_admitted 0 (same.mp hasSwitch)

def equivalence_source :
    Registration equivalenceArena (type_of% (@admits_switch_iff_not_central)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@admits_switch_iff_not_central, rejected, equivalence_rejected⟩
  sensitivity := sensitivity equivalenceLaw actual rejected equivalence_rejected
  dependence := dependence

def equivalence_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@admits_switch_iff_not_central) (Realization sig) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.SteinerSwitchCentre.admits_switch_iff_not_central.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre.equivalence_source
  realizationSource := none
  generated := false
  arena := .source ⟨equivalenceArena⟩
  objectArena := .source ⟨equivalenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equivalenceArena ⟨equivalence_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


def countLaw (R : Realization sig) : Prop :=
  ∀ {r : ℕ} {S : Set (Set (Fin (r + 1)))}
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b),
    let _ : Mul (Option (Fin (r + 1))) := steinerMul valid complete
    ({q | R.readout () r S q} : Set (Fin (r + 1))).ncard =
      r + 2 - (Set.center (Option (Fin (r + 1)))).ncard

abbrev countArena : Arena := ⟨sig, countLaw⟩

private theorem count_rejected : ¬ countLaw rejected := by
  intro h
  let _ : Mul (Option (Fin 9)) := steinerMul affinePlane_valid affinePlane_complete
  have zero := h affinePlane_valid affinePlane_complete
  change (∅ : Set (Fin 9)).ncard = 8 + 2 - (Set.center (Option (Fin 9))).ncard at zero
  rw [Set.ncard_empty] at zero
  have nonempty : ({q | AdmitsSwitch affinePlane q} : Set (Fin 9)).Nonempty :=
    ⟨0, (admits_switch_iff_not_central affinePlane_valid affinePlane_complete 0).mpr
      affine_noncentral⟩
  have eq := ncard_admits_switch affinePlane_valid affinePlane_complete
  exact (nonempty.ncard_pos).ne' (eq.trans zero.symm)

def count_source : Registration countArena (type_of% (@ncard_admits_switch)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ncard_admits_switch, rejected, count_rejected⟩
  sensitivity := sensitivity countLaw actual rejected count_rejected
  dependence := dependence

def count_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@ncard_admits_switch) (Realization sig) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.SteinerSwitchCentre.ncard_admits_switch.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre.count_source
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨count_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg",
        "arg", "body", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
