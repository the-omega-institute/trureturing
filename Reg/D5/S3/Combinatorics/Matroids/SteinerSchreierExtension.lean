import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
import D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.ZMod.Basic

/-! # Source registration for prescribed Steiner extension returns -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension

open Function LeanInformationAudit SimpleGraph
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)
open _root_.D5.S3.Combinatorics.Matroids
open _root_.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
  (affinePlane_valid affinePlane_complete)
open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
open SteinerAlternatingSwitches (pivotGraph point_deleted_successful_starts SuccessfulStart)
open SteinerMatchingTranslations (translate_involutive)
open PointDeletedSteinerSwitch (pointDeletedFamily)
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered)

universe u v

noncomputable section

abbrev sig := signature (Type u) (fun L => L) (fun L => L)

def actual : Realization sig :=
  realize sig (fun _ _ x => x) (fun a => nomatch a)

def rejected : Realization sig := by
  classical
  exact realize sig (fun _ L x => if h : ∃ y : L, y ≠ x then Classical.choose h else x)
    (fun a => nomatch a)

def law (R : Realization sig.{u}) : Prop :=
  ∀ {L : Type u} {A : Type v} [Finite L] [Mul L] [AddCommGroup A]
    (G : SimpleGraph L) (e p q : L)
    (_unit : ∀ x : L, e * x = x) (_comm : ∀ x y : L, x * y = y * x)
    (_invol : ∀ x y : L, x * (x * y) = y)
    (_twice : ∀ a : A, a + a = 0) (_centreless : Set.center L = {e})
    (_hpq : p ≠ q) (_hp : p ≠ e) (_hq : q ≠ e)
    (_edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v)
    (t : {C : G.ConnectedComponent // C ≠ G.connectedComponentMk e} → A),
    ∃ labels : Set L → A,
      letI := extensionMul e labels
      let g : L → L := fun y => p * (q * y)
      let f : L × A → L × A := fun y => (p, 0) * ((q, 0) * y)
      (∀ x : L × A, (e, 0) * x = x) ∧
      (∀ x y : L × A, x * y = y * x) ∧
      (∀ x y : L × A, x * (x * y) = y) ∧
      Set.center (L × A) = {x | x.1 = e} ∧
      (∀ x, G.connectedComponentMk x = G.connectedComponentMk e →
        ∀ a : A, f^[minimalPeriod g x] (x, a) = (R.readout () L x, a)) ∧
      ∀ (C : {C : G.ConnectedComponent // C ≠ G.connectedComponentMk e}) (x : L),
        G.connectedComponentMk x = C.val →
          ∀ a : A, f^[minimalPeriod g x] (x, a) = (x, a + t C)

abbrev arena : Arena := ⟨sig, law.{u,v}⟩

private theorem rejected_ne {L : Type u} [Nontrivial L] (x : L) :
    rejected.readout () L x ≠ x := by
  classical
  have hx := exists_ne x
  change (if h : ∃ y : L, y ≠ x then Classical.choose h else x) ≠ x
  rw [dif_pos hx]
  exact Classical.choose_spec hx

private theorem affine_noncentral_at {S : Set (Set (Fin 9))} (valid : IsPartialSteiner S)
    (complete : ∀ a b, a ≠ b → Covered S a b) (q : Fin 9) :
    letI := steinerMul valid complete
    some q ∉ Set.center (Option (Fin 9)) := by
  letI := steinerMul valid complete
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
    (complete : ∀ a b, a ≠ b → Covered S a b) : ¬ law.{u,v} rejected := by
  intro h
  let B := Option (Fin 9)
  letI := steinerMul valid complete
  let L := ULift.{u} B
  let A := ULift.{v} (ZMod 2)
  let e : L := ULift.up none
  let p : L := ULift.up (some (0 : Fin 9))
  let q : L := ULift.up (some ((0 : Fin 9).succAbove (0 : Fin 8)))
  let G : SimpleGraph L := (pivotGraph valid complete 0 0).comap ULift.down
  have unit (x : L) : e * x = x := ULift.ext rfl
  have comm (x y : L) : x * y = y * x :=
    ULift.ext (product_comm valid complete x.down y.down)
  have invol (x y : L) : x * (x * y) = y := by
    apply ULift.ext
    change x.down * (x.down * y.down) = y.down
    cases hd : x.down with
    | none => rfl
    | some w => exact translate_involutive valid complete w y.down
  have twice (a : A) : a + a = 0 := by
    apply ULift.ext
    exact (show ∀ j : ZMod 2, j + j = 0 by decide) a.down
  have centreless : Set.center L = {e} := by
    ext x
    constructor
    · intro hx
      let proj : L →ₙ* B := ⟨ULift.down, fun _ _ => rfl⟩
      have hs : Surjective proj := fun b => ⟨ULift.up b, rfl⟩
      have hb := Set.mem_center_iff.mpr ((Set.mem_center_iff.mp hx).map (f := proj) hs)
      have hd : x.down = none := by
        change x.down ∈ Set.center B at hb
        cases hx' : x.down with
        | none => rfl
        | some w => exact (affine_noncentral_at valid complete w (hx' ▸ hb)).elim
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
  obtain ⟨labels, _, _, _, _, wrong, _⟩ :=
    h (A := A) G e p q unit comm invol twice centreless hpq hp hq edges (fun _ => 0)
  letI := extensionMul e labels
  let g : L → L := fun y => p * (q * y)
  let f : L × A → L × A := fun y => (p, 0) * ((q, 0) * y)
  have semi : Semiconj Prod.fst f g := fun _ => rfl
  have wrongBase := congrArg Prod.fst (wrong e rfl (0 : A))
  change Prod.fst (f^[minimalPeriod g e] (e, 0)) = rejected.readout () L e at wrongBase
  rw [show Prod.fst (f^[minimalPeriod g e] (e, 0)) = g^[minimalPeriod g e] e
        from (semi.iterate_right _) _,
      show g^[minimalPeriod g e] e = e from isPeriodicPt_minimalPeriod g e] at wrongBase
  exact rejected_ne e wrongBase.symm

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro role
  refine ⟨ULift.{u} Bool, ULift.up false, ULift.up true, ?_⟩
  intro eq
  exact Bool.noConfusion (congrArg ULift.down eq)

def source : Registration arena.{u,v} (type_of% (@realizeSchreierReturns.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@realizeSchreierReturns, rejected,
    rejected_for affinePlane_valid affinePlane_complete⟩
  sensitivity := sensitivity law actual rejected
    (rejected_for affinePlane_valid affinePlane_complete)
  dependence := dependence


def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@realizeSchreierReturns.{u,v}) (Realization sig.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.SteinerSchreierExtension.realizeSchreierReturns.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension.source
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
    owner := `D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg",
        "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 22
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension
