import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
import D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
import Mathlib.Algebra.Group.PUnit

/-! # Source registration for labelled Steiner switch counts -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount

open LeanInformationAudit SimpleGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)
open _root_.D5.S3.Combinatorics.Matroids
open _root_.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
  (affinePlane_valid affinePlane_complete)
open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
open SteinerAlternatingSwitches (pivotGraph point_deleted_successful_starts SuccessfulStart)
open SteinerMatchingTranslations (translate_involutive)
open PointDeletedSteinerSwitch (pointDeletedFamily)
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)

universe u v

noncomputable section

abbrev sig := signature Unit (fun _ => Type v) (fun _ => ℕ)

def actual : Realization sig.{v} :=
  realize sig (fun _ _ A => Nat.card A) (fun anchor => nomatch anchor)

def rejected : Realization sig.{v} :=
  realize sig (fun _ _ _ => 0) (fun anchor => nomatch anchor)

def law (R : Realization sig.{v}) : Prop :=
  ∀ {L : Type u} {A : Type v} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] (G : SimpleGraph L) (e p q : L)
    (_unit : ∀ x : L, e * x = x) (_comm : ∀ x y : L, x * y = y * x)
    (_invol : ∀ x y : L, x * (x * y) = y)
    (_twice : ∀ a : A, a + a = 0) (_centreless : Set.center L = {e})
    (_hpq : p ≠ q) (_hp : p ≠ e) (_hq : q ≠ e)
    (_edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (t : {C : G.ConnectedComponent // C ≠ G.connectedComponentMk e} → A),
    ∃ (r : ℕ) (label : Option (Fin (r + 1)) ≃ L × A)
      (i : Fin (r + 1)) (v : Fin r)
      (S : Set (Set (Fin (r + 1)))) (m : Fin r → Fin r),
      label none = (e, 0) ∧ label (some i) = (p, 0) ∧ label (some (i.succAbove v)) = (q, 0) ∧
      IsPartialSteiner S ∧ (∀ a b : Fin (r + 1), a ≠ b → Covered S a b) ∧
      (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
      let g : L → L := fun x => p * (q * x)
      ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard =
        R.readout () () A * ({x | g (g x) ≠ x ∨
          ∃ h : G.connectedComponentMk x ≠ G.connectedComponentMk e,
            t ⟨G.connectedComponentMk x, h⟩ ≠ 0} : Set L).ncard

abbrev arena : Arena := ⟨sig, law.{u,v}⟩

private theorem affine_not_central (i : Fin 9) :
    let _ := steinerMul affinePlane_valid affinePlane_complete
    some i ∉ Set.center (Option (Fin 9)) := by
  let _ := steinerMul affinePlane_valid affinePlane_complete
  apply (admits_switch_iff_not_central affinePlane_valid affinePlane_complete i).mp
  obtain ⟨_, m, leave, audit⟩ :=
    point_deleted_successful_starts _ affinePlane_valid affinePlane_complete i
  have six := (audit 0).2.2 (by decide)
  have existsGood := (Set.ncard_pos (Set.toFinite _)).mp ((show 0 < 6 by decide).trans_le six)
  obtain ⟨a, ha⟩ := existsGood
  exact ⟨m, leave, 0, a, ha⟩

private theorem rejected_law : ¬ law.{u,v} rejected := by
  intro bound
  let B := Option (Fin 9)
  let _ := steinerMul affinePlane_valid affinePlane_complete
  let L := ULift.{u} B
  let A := PUnit.{v+1}
  let e : L := ULift.up none
  let p : L := ULift.up (some (0 : Fin 9))
  let q : L := ULift.up (some ((0 : Fin 9).succAbove (0 : Fin 8)))
  let G : SimpleGraph L := (pivotGraph affinePlane_valid affinePlane_complete 0 0).comap ULift.down
  have unit (x : L) : e * x = x := ULift.ext rfl
  have comm (x y : L) : x * y = y * x :=
    ULift.ext (product_comm affinePlane_valid affinePlane_complete x.down y.down)
  have invol (x y : L) : x * (x * y) = y := by
    apply ULift.ext
    change x.down * (x.down * y.down) = y.down
    cases hd : x.down with
    | none => rfl
    | some w => exact translate_involutive affinePlane_valid affinePlane_complete w y.down
  have centreless : Set.center L = {e} := by
    ext x
    constructor
    · intro hx
      let proj : L →ₙ* B := ⟨ULift.down, fun _ _ => rfl⟩
      have hs : Function.Surjective proj := fun b => ⟨ULift.up b, rfl⟩
      have hb := Set.mem_center_iff.mpr ((Set.mem_center_iff.mp hx).map (f := proj) hs)
      have hd : x.down = none := by
        change x.down ∈ Set.center B at hb
        cases hx' : x.down with
        | none => rfl
        | some w => exact (affine_not_central w (hx' ▸ hb)).elim
      exact ULift.ext hd
    · intro hx
      change x = e at hx
      subst x
      have rightUnit (x : L) : x * e = x := (comm x e).trans (unit x)
      exact ⟨fun x => comm e x, fun x y => by rw [unit, unit],
        fun x y => by rw [rightUnit, rightUnit]⟩
  have hpq : p ≠ q := by
    intro eq
    have down : some (0 : Fin 9) = some ((0 : Fin 9).succAbove (0 : Fin 8)) :=
      congrArg ULift.down eq
    exact Fin.succAbove_ne _ _ (Option.some.inj down).symm
  have hp : p ≠ e := by
    intro eq
    have h : some (0 : Fin 9) = (none : B) := congrArg ULift.down eq
    cases h
  have hq : q ≠ e := by
    intro eq
    have h : some ((0 : Fin 9).succAbove (0 : Fin 8)) = (none : B) := congrArg ULift.down eq
    cases h
  have edges (x y : L) : G.Adj x y ↔ p * x = y ∨ q * x = y := by
    change (p.down * x.down = y.down ∨ q.down * x.down = y.down) ↔ _
    exact or_congr ⟨ULift.ext, congrArg ULift.down⟩ ⟨ULift.ext, congrArg ULift.down⟩
  obtain ⟨r, label, i, v, S, m, _, _, _, valid, complete, leave, noStarts⟩ :=
    bound (A := A) G e p q unit comm invol (fun _ => Subsingleton.elim _ _) centreless
      hpq hp hq edges (fun _ => 0)
  have size := Nat.card_congr label
  have rEq : r = 8 := by
    change Nat.card (Option (Fin (r + 1))) = Nat.card (ULift.{u} (Option (Fin 9)) × A) at size
    dsimp only [A] at size
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin,
      Fintype.card_prod, Fintype.card_ulift, Fintype.card_punit, mul_one] at size
    omega
  have divisible : 4 ∣ r := rEq.symm ▸ (by decide : 4 ∣ 8)
  obtain ⟨_, canonical, canonicalLeave, starts⟩ :=
    point_deleted_successful_starts S valid complete i
  have sameMatching : canonical = m := funext fun a =>
    ((leave a (canonical a)).mp ((canonicalLeave a (canonical a)).mpr rfl)).symm
  subst canonical
  have six := (starts v).2.2 divisible
  change ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard =
    0 * _ at noStarts
  omega

private theorem dependence : ObservationalDependence sig.{v} actual := by
  intro role
  refine ⟨(), PUnit.{v+1}, ULift.{v} Bool, ?_⟩
  change Nat.card (PUnit.{v+1}) ≠ Nat.card (ULift.{v} Bool)
  simp [Nat.card_eq_fintype_card]

def source : Registration arena.{u,v} (type_of% (@realizeLabelledSwitchCount.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realizeLabelledSwitchCount, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@realizeLabelledSwitchCount.{u,v}) (Realization sig.{v}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount.realizeLabelledSwitchCount.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount.source
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
    owner := `D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg",
        "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
