import Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
import D5.S3.Combinatorics.Matroids.SteinerAffineSwitchCount
import Mathlib.Algebra.Module.PUnit
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.Fintype.BigOperators

/-! Source registration for affine Steiner switch counts. -/

namespace Reg.D5.S3.Combinatorics.Matroids.SteinerAffineSwitchCount

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Matroids
open _root_.D5.S3.Combinatorics.Matroids.SteinerAffineSwitchCount
open SteinerSchreierExtension (extensionMul)
open SteinerMatchingTranslations (translate)
open SteinerAlternatingSwitches (SuccessfulStart point_deleted_successful_starts)
open PointDeletedSteinerSwitch (pointDeletedFamily)
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open RankThreeSaturatedTopGap (Covered Uncovered)
open _root_.Reg.D5.S3.Combinatorics.Matroids.SteinerSchreierSwitchCount
  (sig actual rejected)
open _root_.Reg.Support.UniverseSingleReadout (sensitivity)

universe u v

noncomputable section

def law (R : Realization sig.{v}) : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [DecidableEq V] {A : Type v} [Fintype V] [Finite A]
    [AddCommGroup A] [Module (ZMod 2) A]
    (_three : ∀ a : V, a + a = -a) (_size : 3 < Fintype.card V)
    (labels : Set (Option V) → A),
    letI : Mul (Option V) := ⟨mul⟩
    letI := extensionMul (none : Option V) labels
    ∃ (r : ℕ) (label : Option (Fin (r + 1)) ≃ Option V × A)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b),
      label none = (none, 0) ∧ Set.center (Option V × A) = {x | x.1 = none} ∧
      (∀ i a, label (translate valid cover i a) = label (some i) * label a) ∧
      ∀ p q : V, p ≠ q → ∃ (i : Fin (r + 1)) (v : Fin r) (m : Fin r → Fin r),
        label (some i) = (some p, 0) ∧ label (some (i.succAbove v)) = (some q, 0) ∧
        (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
        ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard =
          R.readout () () A * (Fintype.card V - 3)

abbrev arena : Arena := ⟨sig, law.{u,v}⟩

private theorem rejected_law : ¬ law.{u,v} rejected := by
  intro bound
  let V := ULift.{u} (Fin 2 → ZMod 3)
  let A := PUnit.{v+1}
  have three (x : V) : x + x = -x := by
    apply ULift.ext
    funext i
    exact (by decide : ∀ z : ZMod 3, z + z = -z) (x.down i)
  have cardV : Fintype.card V = 9 := by
    change Fintype.card (ULift (Fin 2 → ZMod 3)) = 9
    rw [Fintype.card_ulift, Fintype.card_pi_const, ZMod.card]
    decide
  have size : 3 < Fintype.card V := cardV.symm ▸ (by decide : 3 < 9)
  let labels : Set (Option V) → A := fun _ => 0
  obtain ⟨r, label, S, valid, cover, _, _, _, profiles⟩ :=
    bound (V := V) (A := A) three size labels
  let p : V := ULift.up (fun _ => 0)
  let q : V := ULift.up (fun _ => 1)
  have different : p ≠ q := by
    intro eq
    have zeroOne : (0 : ZMod 3) = 1 :=
      congrArg (fun x : V => x.down 0) eq
    exact (by decide : (0 : ZMod 3) ≠ 1) zeroOne
  obtain ⟨i, pivot, m, _, _, leave, noStarts⟩ := profiles p q different
  have sizeOfNumbering := Nat.card_congr label
  have rEq : r = 8 := by
    dsimp only [A] at sizeOfNumbering
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin,
      Fintype.card_prod, cardV, Fintype.card_punit, mul_one] at sizeOfNumbering
    omega
  have divisible : 4 ∣ r := rEq.symm ▸ (by decide : 4 ∣ 8)
  obtain ⟨_, canonical, canonicalLeave, starts⟩ :=
    point_deleted_successful_starts S valid cover i
  have same : canonical = m := funext fun a =>
    ((leave a (canonical a)).mp ((canonicalLeave a (canonical a)).mpr rfl)).symm
  subst canonical
  have six := (starts pivot).2.2 divisible
  simp only [rejected, realize, zero_mul] at noStarts
  omega

def source : Registration arena.{u,v} (type_of% (@labelledAffineSwitchCount.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@labelledAffineSwitchCount, rejected, rejected_law⟩
  sensitivity := sensitivity law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨(), PUnit.{v+1}, ULift.{v} Bool, ?_⟩
    change Nat.card (PUnit.{v+1}) ≠ Nat.card (ULift.{v} Bool)
    simp [Nat.card_eq_fintype_card]


def affineCountRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@labelledAffineSwitchCount.{u,v}) (Realization sig.{v}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Matroids.SteinerAffineSwitchCount.labelledAffineSwitchCount.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.SteinerAffineSwitchCount.source
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
    owner := `D5.S3.Combinatorics.Matroids.SteinerAffineSwitchCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "arg", "arg", "body", "body", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Matroids.SteinerAffineSwitchCount
