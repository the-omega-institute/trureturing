import Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
import D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
import Mathlib.Algebra.Module.PUnit

/-! # Source registration for simultaneous Steiner switch counts -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport

open Function LeanInformationAudit Module Submodule
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids
open _root_.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
open SteinerSchreierExtension (extensionMul)
open SteinerReturnDependencies (returnRow)
open SteinerSwitchCentre (steinerMul product_comm)
open SteinerMatchingTranslations (translate_involutive)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchCentre
  (affinePlane_valid affinePlane_complete)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
  (sig actual rejected affine_not_central)
open _root_.Reg.Support.UniverseSingleReadout (sensitivity)

universe j u v

noncomputable section

def commonCountLaw (R : Realization sig.{v}) : Prop :=
  ∀ {J : Type j} {L : Type u} {A : Type v} [Finite L] [Finite A] [Mul L]
    [AddCommGroup A] [Module (ZMod 2) A] [Module.Finite (ZMod 2) A]
    (e : L) (p q : J → L)
    (_unit : ∀ x : L, e * x = x) (_comm : ∀ x y : L, x * y = y * x)
    (_invol : ∀ x y : L, x * (x * y) = y) (_centreless : Set.center L = {e})
    (_different : ∀ i, p i ≠ q i) (counts : J → ℕ),
    (∃ labels : Set L → A,
      letI := extensionMul e labels
      ∀ i, ({y : L × A | (q i, 0) * ((p i, 0) * y) ≠
        (p i, 0) * ((q i, 0) * y)} : Set (L × A)).ncard = counts i) ↔
      ∃ H : Submodule (ZMod 2) (Set L →₀ ZMod 2),
        finrank (ZMod 2) ((Set L →₀ ZMod 2) ⧸ H) ≤ finrank (ZMod 2) A ∧
        ∀ i, R.readout () () A * ({x : L |
          let g := fun y : L => p i * (q i * y)
          g (g x) ≠ x ∨ returnRow e (p i) (q i) x ∉ H} : Set L).ncard = counts i

abbrev commonCountArena : Arena := ⟨sig, commonCountLaw.{j,u,v}⟩

private abbrev AffineLoop := ULift.{u} (Option (Fin 9))

private instance : Mul AffineLoop.{u} :=
  letI := steinerMul affinePlane_valid affinePlane_complete
  inferInstanceAs (Mul (ULift (Option (Fin 9))))

private abbrev affineIdentity : AffineLoop.{u} := ULift.up none

private theorem affine_unit (x : AffineLoop.{u}) : affineIdentity * x = x := rfl

private theorem affine_comm (x y : AffineLoop.{u}) : x * y = y * x :=
  ULift.ext (product_comm affinePlane_valid affinePlane_complete x.down y.down)

private theorem affine_invol (x y : AffineLoop.{u}) : x * (x * y) = y := by
  letI := steinerMul affinePlane_valid affinePlane_complete
  apply ULift.ext
  change x.down * (x.down * y.down) = y.down
  cases h : x.down with
  | none => rfl
  | some i => exact translate_involutive affinePlane_valid affinePlane_complete i y.down

private theorem affine_centreless : Set.center AffineLoop.{u} = {affineIdentity} := by
  letI := steinerMul affinePlane_valid affinePlane_complete
  ext x
  constructor
  · intro central
    let proj : AffineLoop →ₙ* Option (Fin 9) := ⟨ULift.down, fun _ _ => rfl⟩
    have onto : Function.Surjective proj := fun y => ⟨ULift.up y, rfl⟩
    have down := Set.mem_center_iff.mp central |>.map (f := proj) onto
    have h : x.down = none := by
      change IsMulCentral x.down at down
      cases hx : x.down with
      | none => rfl
      | some i => exact (affine_not_central i (hx ▸ down)).elim
    exact ULift.ext h
  · intro equal
    change x = affineIdentity at equal
    subst x
    have rightUnit (y : AffineLoop) : y * affineIdentity = y :=
      (affine_comm y affineIdentity).trans (affine_unit y)
    exact ⟨affine_comm affineIdentity, fun _ _ => by rw [affine_unit, affine_unit],
      fun _ _ => by rw [rightUnit, rightUnit]⟩

private theorem affine_noncommuting :
    ∃ p q x : AffineLoop.{u}, q * (p * x) ≠ p * (q * x) := by
  let p : AffineLoop := ULift.up (some 0)
  suffices ∃ q x : AffineLoop, q * (p * x) ≠ p * (q * x) by
    obtain ⟨q, x, h⟩ := this
    exact ⟨p, q, x, h⟩
  by_contra! commutes
  have central : p ∈ Set.center AffineLoop := by
    refine ⟨affine_comm p, ?_, ?_⟩
    · intro x y
      calc
        p * (x * y) = p * (y * x) := congrArg (p * ·) (affine_comm x y)
        _ = y * (p * x) := (commutes y x).symm
        _ = (p * x) * y := affine_comm _ _
    · intro x y
      calc
        (x * y) * p = p * (x * y) := affine_comm _ _
        _ = x * (p * y) := (commutes x y).symm
        _ = x * (y * p) := congrArg (x * ·) (affine_comm p y)
  rw [affine_centreless] at central
  exact Option.some_ne_none _ (congrArg ULift.down (Set.mem_singleton_iff.mp central))

private theorem commonCount_rejected : ¬ commonCountLaw.{j,u,v} rejected := by
  intro bound
  let J := PUnit.{j+1}
  let A := PUnit.{v+1}
  letI : Module.Finite (ZMod 2) A :=
    Module.Finite.of_surjective (0 : ZMod 2 →ₗ[ZMod 2] A) (fun a => ⟨0, Subsingleton.elim _ a⟩)
  obtain ⟨p, q, x, noncommuting⟩ := affine_noncommuting.{u}
  have different : p ≠ q := by
    intro equal
    subst q
    exact noncommuting rfl
  let labels : Set AffineLoop → A := fun _ => 0
  letI := extensionMul affineIdentity labels
  let successful : Set (AffineLoop × A) :=
    {y | (q, 0) * ((p, 0) * y) ≠ (p, 0) * ((q, 0) * y)}
  have good : (x, (0 : A)) ∈ successful :=
    fun equal => noncommuting (congrArg Prod.fst equal)
  have positive : 0 < successful.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, good⟩
  obtain ⟨H, _, noStarts⟩ := (bound (J := J) (A := A) affineIdentity (fun _ => p)
    (fun _ => q) affine_unit affine_comm affine_invol affine_centreless (fun _ => different)
    (fun _ => successful.ncard)).mp ⟨labels, fun _ => rfl⟩
  have impossible := noStarts PUnit.unit
  simp only [rejected, realize, zero_mul] at impossible
  exact (Nat.ne_of_gt positive) impossible.symm

private theorem cardinality_dependence : ObservationalDependence sig.{v} actual := by
  intro role
  refine ⟨(), PUnit.{v+1}, ULift.{v} Bool, ?_⟩
  change Nat.card (PUnit.{v+1}) ≠ Nat.card (ULift.{v} Bool)
  simp [Nat.card_eq_fintype_card]

def commonCountSource :
    Registration commonCountArena.{j,u,v} (type_of% (@commonSwitchCounts.{j,u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@commonSwitchCounts, rejected, commonCount_rejected⟩
  sensitivity := sensitivity commonCountLaw actual rejected commonCount_rejected
  dependence := cardinality_dependence

def commonCountRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@commonSwitchCounts.{j,u,v}) (Realization sig.{v}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Matroids.SteinerSwitchSupport.commonSwitchCounts.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport.commonCountSource
  realizationSource := none
  generated := false
  arena := .source ⟨commonCountArena⟩
  objectArena := .source ⟨commonCountArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source commonCountArena ⟨commonCountSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.SteinerSwitchSupport
