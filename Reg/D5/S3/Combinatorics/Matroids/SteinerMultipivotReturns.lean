import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
import Mathlib.Data.ZMod.Basic
import D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
import Mathlib.Algebra.Group.ULift

/-! # Registration of the simultaneous return range and the centreless obstruction -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns

open Function LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
open _root_.D5.S3.Combinatorics.Matroids.SteinerSchreierExtension (extensionMul)
open _root_.Reg.Support.UniverseSingleReadout (signature sensitivity)

universe u v

noncomputable section

private def other {A : Type u} (w : A) : A := by
  classical
  exact if h : ∃ a : A, a ≠ w then Classical.choose h else w

private theorem other_ne {A : Type u} {x : A} (hx : ∃ a : A, a ≠ x) : other x ≠ x := by
  classical
  unfold other
  rw [dite_eq_left hx]
  exact Classical.choose_spec hx

namespace ReturnRange

abbrev sig := signature (Type u) (fun A => A) (fun A => A)

def actual : Realization sig.{u} :=
  realize sig (fun _ _ w => w) (fun anchor => nomatch anchor)

def rejected : Realization sig.{u} :=
  realize sig (fun _ _ w => other w) (fun anchor => nomatch anchor)

def law (R : Realization sig.{u}) : Prop :=
  ∀ {A : Type u} {L : Type v} [AddCommGroup A] [Mul L]
    (b : BitVec 3 ↪ L) (_mul : ∀ x y, b (x ^^^ y) = b x * b y)
    (_twice : ∀ x : A, x + x = 0) (u v w : A),
    (∃ labels : Set L → A,
      letI := extensionMul (b 0) labels
      ∀ i : Fin 4, ∀ a : A,
        let x := b (BitVec.ofNat 3 (4 + i.val))
        (pairLift (b 1) (b 2))^[2] (x, a) = (x, a + u) ∧
        (pairLift (b 1) (b 3))^[2] (x, a) = (x, a + v) ∧
        (pairLift (b 2) (b 3))^[2] (x, a) = (x, a + w)) ↔ (u + v) + R.readout () A w = 0

abbrev arena : Arena := ⟨sig, law.{u,v}⟩

private theorem rejected_law : ¬ law.{u,v} rejected := by
  intro rule
  let A := ULift.{u} (ZMod 2)
  let L := ULift.{v} (BitVec 3)
  let _ : Mul L := ⟨fun x y => ULift.up (x.down ^^^ y.down)⟩
  let cube : BitVec 3 ↪ L := ⟨ULift.up, fun {_ _} h => congrArg ULift.down h⟩
  have mul (x y : BitVec 3) : cube (x ^^^ y) = cube x * cube y := rfl
  have twice (a : A) : a + a = 0 :=
    ULift.ext ((show ∀ j : ZMod 2, j + j = 0 by decide) a.down)
  have altered : rejected.readout () A (0 : A) ≠ 0 := by
    classical
    have hn : ∃ a : A, a ≠ 0 := ⟨ULift.up 1, by decide⟩
    change other (0 : A) ≠ (0 : A)
    unfold other
    rw [dite_eq_left hn]
    exact Classical.choose_spec hn
  have zeroReturn := (simultaneousReturns cube mul twice (0 : A) 0 0).mpr (by simp)
  have incompatible := (rule cube mul twice (0 : A) 0 0).mp zeroReturn
  exact altered (by simpa only [zero_add] using incompatible)

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro role
  refine ⟨ULift.{u} Bool, ULift.up false, ULift.up true, ?_⟩
  intro h
  exact Bool.noConfusion (congrArg ULift.down h)

def source : Registration arena.{u,v} (type_of% (@simultaneousReturns.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simultaneousReturns, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@simultaneousReturns.{u,v}) (Realization sig.{u}) Type Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns.simultaneousReturns.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns.ReturnRange.source
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
    owner := `D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "arg", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ReturnRange

namespace CentrelessModel

open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
open _root_.D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches
  (SuccessfulStart point_deleted_successful_starts)
open _root_.D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations (translate_involutive)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
  (affinePlane_valid affinePlane_complete)

abbrev sig := signature (Type u) (fun L => L) (fun L => L)

def actual : Realization sig.{u} := realize sig (fun _ _ e => e) (fun a => nomatch a)

def rejected : Realization sig.{u} := realize sig (fun _ _ e => other e) (fun a => nomatch a)

def law (R : Realization sig.{u}) : Prop :=
  ∀ {L : Type u} [Mul L] (e p : L)
    (_unit : ∀ x : L, e * x = x) (_comm : ∀ x y : L, x * y = y * x)
    (_invol : ∀ x y : L, x * (x * y) = y)
    (_centre : Set.center L = {e}) (_hp : p ≠ e),
    ∃ b : BitVec 3 ↪ L × L × L, b 0 = (R.readout () L e, e, e) ∧
      Set.center (L × L × L) = {b 0} ∧
      ∀ x y : BitVec 3, b (x ^^^ y) = b x * b y

abbrev arena : Arena := ⟨sig, law.{u}⟩

private theorem rejected_law : ¬ law.{u} rejected := by
  intro obstruction
  let B := Option (Fin 9)
  let _ := steinerMul affinePlane_valid affinePlane_complete
  let L := ULift.{u} B
  let e : L := ULift.up none
  let p : L := ULift.up (some (0 : Fin 9))
  have ne : p ≠ e := by
    intro h
    exact Option.some_ne_none _ (congrArg ULift.down h)
  have unit (x : L) : e * x = x := rfl
  have comm (x y : L) : x * y = y * x :=
    ULift.ext (product_comm affinePlane_valid affinePlane_complete x.down y.down)
  have invol (x y : L) : x * (x * y) = y := by
    apply ULift.ext
    change x.down * (x.down * y.down) = y.down
    cases h : x.down with
    | none => rfl
    | some i => exact translate_involutive affinePlane_valid affinePlane_complete i y.down
  have centre : Set.center L = {e} := by
    ext x
    constructor
    · intro h
      let proj : L →ₙ* B := ⟨ULift.down, fun _ _ => rfl⟩
      have onto : Function.Surjective proj := fun a => ⟨ULift.up a, rfl⟩
      have ctr := Set.mem_center_iff.mpr ((Set.mem_center_iff.mp h).map (f := proj) onto)
      change x.down ∈ Set.center B at ctr
      apply ULift.ext
      cases hx : x.down with
      | none => rfl
      | some i =>
        apply False.elim
        have z := Set.mem_center_iff.mp (hx ▸ ctr)
        have admitted := (admits_switch_iff_not_central affinePlane_valid affinePlane_complete i).mp
        apply admitted _ z
        obtain ⟨_, m, leave, starts⟩ :=
          point_deleted_successful_starts _ affinePlane_valid affinePlane_complete i
        have six := (starts 0).2.2 (by decide)
        have good := (Set.ncard_pos (Set.toFinite _)).mp ((show 0 < 6 by decide).trans_le six)
        obtain ⟨a, ha⟩ := good
        exact ⟨m, leave, 0, a, ha⟩
    · intro h
      change x = e at h
      subst x
      have rightUnit (y : L) : y * e = y := (comm y e).trans (unit y)
      exact ⟨comm e, fun _ _ => by rw [unit, unit], fun _ _ => by rw [rightUnit, rightUnit]⟩
  obtain ⟨b, id, ctr, _⟩ := obstruction e p unit comm invol centre ne
  have central : b 0 ∈ Set.center (L × L × L) := by rw [ctr]; rfl
  rw [id, Set.center_prod, Set.center_prod, centre] at central
  exact other_ne (x := e) ⟨p, ne⟩ central.1

private theorem dependence : ObservationalDependence sig.{u} actual := by
  intro role
  refine ⟨ULift.{u} Bool, ULift.up false, ULift.up true, ?_⟩
  intro h
  exact Bool.noConfusion (congrArg ULift.down h)

def source : Registration arena.{u} (type_of% (@existsCentrelessBooleanCube.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@existsCentrelessBooleanCube, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@existsCentrelessBooleanCube.{u}) (Realization sig.{u}) Type Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns.existsCentrelessBooleanCube.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns.CentrelessModel.source
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
    owner := `D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CentrelessModel

end
end Reg.D5.S3.Combinatorics.Matroids.SteinerMultipivotReturns
