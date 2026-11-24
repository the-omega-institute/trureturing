import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
import D5.S3.Combinatorics.Matroids.SteinerSwitchQuotient

/-! # Source registration for the central quotient of Steiner switches -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchQuotient

open Function Set SimpleGraph LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)
open _root_.D5.S3.Combinatorics.Matroids
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered)
open PointDeletedSteinerSwitch (pointDeletedFamily)
open SteinerAlternatingSwitches (pivotGraph SuccessfulStart point_deleted_successful_starts)
open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchQuotient
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
  (affinePlane_valid affinePlane_complete)

noncomputable section

abbrev sig := signature ℕ (fun r => Fin (r + 1)) (fun r => Option (Fin (r + 1)))

def actual : Realization sig :=
  realize sig (fun _ _ q => some q) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ => none) (fun e => nomatch e)

def law (R : Realization sig) : Prop :=
  ∀ {r : ℕ} {S : Set (Set (Fin (r + 1)))}
    (valid : IsPartialSteiner S) (complete : ∀ a b, a ≠ b → Covered S a b)
    (q : Fin (r + 1)) (v : Fin r),
    let _ := steinerMul valid complete
    let p : Option (Fin (r + 1)) := some q
    let u : Option (Fin (r + 1)) := some (q.succAbove v)
    let Z := Set.center (Option (Fin (r + 1)))
    p ∉ Z → u ∉ Z → (¬ ∃ z ∈ Z, z * u = p) →
    ∃ (B : Type) (proj : Option (Fin (r + 1)) → B) (P Q : B → B)
      (H : SimpleGraph B),
      Surjective proj ∧
      (∀ x y, proj x = proj y ↔ ∃ z ∈ Z, z * x = y) ∧
      Semiconj proj (R.readout () r q * ·) P ∧ Semiconj proj (u * ·) Q ∧
      (∀ x y, H.Adj x y ↔ P x = y ∨ Q x = y) ∧
      (∀ b, P b ≠ Q b) ∧
      ∀ x : Option (Fin (r + 1)), ∃ a ∈ Z,
        let k := minimalPeriod (P ∘ Q) (proj x)
        let d : ℕ := if a = none then 1 else 2
        let G := pivotGraph valid complete q v
        let C := (H.connectedComponentMk (proj x)).supp
        let T := Set.range (fun y : proj ⁻¹' C => G.connectedComponentMk y.val)
        ((fun y => p * (u * y))^[k]) x = a * x ∧
        (G.connectedComponentMk x).supp.ncard = C.ncard * d ∧
        T.ncard * d = Z.ncard

abbrev arena : Arena := ⟨sig, law⟩

private theorem affine_noncentral_at {S : Set (Set (Fin 9))} (valid : IsPartialSteiner S)
    (complete : ∀ a b, a ≠ b → Covered S a b) (q : Fin 9) :
    let _ := steinerMul valid complete
    some q ∉ Set.center (Option (Fin 9)) := by
  let _ := steinerMul valid complete
  apply (admits_switch_iff_not_central valid complete q).mp
  obtain ⟨_, m, leave, counts⟩ := point_deleted_successful_starts S valid complete q
  let good : Set (Fin 8) := {a | SuccessfulStart (pointDeletedFamily S q) m 0 a}
  have six : 6 ≤ good.ncard := (counts 0).2.2 (by decide)
  have nonempty : good.Nonempty := by
    by_contra empty
    rw [Set.not_nonempty_iff_eq_empty.mp empty, Set.ncard_empty] at six
    omega
  obtain ⟨a, ha⟩ := nonempty
  exact ⟨m, leave, 0, a, ha⟩

private theorem rejected_for {S : Set (Set (Fin 9))} (valid : IsPartialSteiner S)
    (complete : ∀ a b, a ≠ b → Covered S a b) : ¬ law rejected := by
  intro h
  let _ := steinerMul valid complete
  let q : Fin 9 := 0
  let v : Fin 8 := 0
  have diff : ¬ ∃ z ∈ Set.center (Option (Fin 9)), z * some (q.succAbove v) = some q := by
    rintro ⟨z, hz, heq⟩
    cases z with
    | none => exact Fin.succAbove_ne q v (Option.some.inj heq)
    | some w => exact affine_noncentral_at valid complete w hz
  obtain ⟨B, proj, P, _, H, _, _, Pidentity, _, edges, _⟩ :=
    h valid complete q v (affine_noncentral_at valid complete q)
      (affine_noncentral_at valid complete (q.succAbove v)) diff
  have fixed : P (proj none) = proj none := (Pidentity none).symm
  exact H.loopless.irrefl _ ((edges _ _).mpr (Or.inl fixed))

private theorem dependence : ObservationalDependence sig actual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  change some (0 : Fin 2) ≠ some (1 : Fin 2)
  decide

def source : Registration arena (type_of% (@point_deleted_component_lifts)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@point_deleted_component_lifts, rejected,
    rejected_for affinePlane_valid affinePlane_complete⟩
  sensitivity := sensitivity law actual rejected (rejected_for affinePlane_valid affinePlane_complete)
  dependence := dependence


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@point_deleted_component_lifts) (Realization sig) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.SteinerSwitchQuotient.point_deleted_component_lifts.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchQuotient.source
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
    owner := `D5.S3.Combinatorics.Matroids.SteinerSwitchQuotient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "fn", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchQuotient
