import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Matroids.SteinerSwitchOrbit
import Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchOrbit

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)
open _root_.D5.S3.Combinatorics.Matroids
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)
open PointDeletedSteinerSwitch (pointDeletedFamily point_deleted_switch)
open SteinerAlternatingSwitches (SuccessfulStart point_deleted_successful_starts)
open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre (AdmitsSwitch admits_switch_iff_not_central steinerMul)
open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchOrbit (successful_starts_dvd_center)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre (affinePlane_valid affinePlane_complete)

noncomputable section

private def triple : Set (Set (Fin 3)) := {Set.univ}

private theorem triple_valid : IsPartialSteiner triple := by
  constructor
  · intro s hs
    have eq : s = Set.univ := hs
    rw [eq]
    simp
  · intro s hs t ht _ _ _ _ _ _ _
    exact (show s = Set.univ from hs).trans (show t = Set.univ from ht).symm

private theorem triple_complete : ∀ a b, a ≠ b → Covered triple a b :=
  fun _ _ _ => ⟨Set.univ, rfl, Set.mem_univ _, Set.mem_univ _⟩

private theorem triple_no_switch (q : Fin 3) : ¬ AdmitsSwitch triple q := by
  rintro ⟨m, leave, v, a, hv, hvm, _⟩
  have hne : m a ≠ a := by
    intro h
    exact ((leave a a).mpr h).1 rfl
  have hall : ∀ v a b : Fin 2, v ≠ a → b ≠ a → v = b := by decide
  exact hvm (hall _ _ _ hv hne)

private theorem triple_center_large :
    let _ := steinerMul triple_valid triple_complete
    2 ≤ (Set.center (Option (Fin 3))).ncard := by
  classical
  let _ := steinerMul triple_valid triple_complete
  have central (q : Fin 3) : some q ∈ Set.center (Option (Fin 3)) := by
    by_contra hn
    exact triple_no_switch q ((admits_switch_iff_not_central triple_valid triple_complete q).mpr hn)
  calc
    2 = ({some (0 : Fin 3), some 1} : Set (Option (Fin 3))).ncard := by simp
    _ ≤ _ := Set.ncard_le_ncard (by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | h
      · exact central 0
      · have hx1 : x = some 1 := h
        exact hx1 ▸ central 1)

abbrev Params := Σ r : ℕ, Σ _q : Fin (r + 1), Σ _m : Fin r → Fin r, Fin r

abbrev sig :=
  signature Params (fun p => Set (Set (Fin (p.1 + 1)))) (fun p => Set (Fin p.1))

def actual : Realization sig :=
  realize sig (fun _ p S => {a | SuccessfulStart (pointDeletedFamily S p.2.1) p.2.2.1 p.2.2.2 a})
    (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ => {a | a.val = 0}) (fun e => nomatch e)

def law (R : Realization sig) : Prop :=
  ∀ {r : ℕ} (q : Fin (r + 1)) (m : Fin r → Fin r) (v : Fin r)
    (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
    (complete : ∀ a b, a ≠ b → Covered S a b)
    (_leave : ∀ a b, Uncovered (pointDeletedFamily S q) a b ↔ m a = b),
    let _ := steinerMul valid complete
    (Set.center (Option (Fin (r + 1)))).ncard ∣ (R.readout () ⟨r, q, m, v⟩ S).ncard

abbrev arena : Arena := ⟨sig, law⟩

private theorem law_rejected : ¬ law rejected := by
  intro h
  obtain ⟨_, m, _, _, leave, _⟩ := point_deleted_switch triple triple_valid triple_complete 0
  have witness := h 0 m 0 triple triple_valid triple_complete leave
  let _ := steinerMul triple_valid triple_complete
  change (Set.center (Option (Fin 3))).ncard ∣ ({a : Fin 2 | a.val = 0} : Set _).ncard at witness
  have one : ({a : Fin 2 | a.val = 0} : Set _) = {0} := by
    ext a
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  rw [one, Set.ncard_singleton, Nat.dvd_one] at witness
  have lower := triple_center_large
  omega

private theorem dependence_for {S : Set (Set (Fin 9))} (valid : IsPartialSteiner S)
    (complete : ∀ a b, a ≠ b → Covered S a b) : ObservationalDependence sig actual := by
  intro i
  obtain ⟨_, m, _, counts⟩ := point_deleted_successful_starts S valid complete (0 : Fin 9)
  let good : Set (Fin 8) := {a | SuccessfulStart (pointDeletedFamily S 0) m 0 a}
  have size : 6 ≤ good.ncard := (counts 0).2.2 (by decide)
  have nonempty : good.Nonempty := by
    by_contra empty
    rw [Set.not_nonempty_iff_eq_empty.mp empty, Set.ncard_empty] at size
    omega
  obtain ⟨a, ha⟩ := nonempty
  refine ⟨⟨8, 0, m, 0⟩, S, ∅, fun eq => ?_⟩
  have pointwise : SuccessfulStart (pointDeletedFamily S 0) m 0 a =
      SuccessfulStart (pointDeletedFamily (∅ : Set (Set (Fin 9))) 0) m 0 a :=
    congrFun eq a
  have impossible := pointwise.mp ha
  obtain ⟨_, _, b, _, hb, _, _⟩ := impossible
  simp [pointDeletedFamily] at hb

def source : Registration arena (type_of% (@successful_starts_dvd_center)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@successful_starts_dvd_center, rejected, law_rejected⟩
  sensitivity := sensitivity law actual rejected law_rejected
  dependence := dependence_for affinePlane_valid affinePlane_complete

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@successful_starts_dvd_center) (Realization sig) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.SteinerSwitchOrbit.successful_starts_dvd_center.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchOrbit.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SteinerSwitchOrbit
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchOrbit
