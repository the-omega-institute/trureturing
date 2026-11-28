import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ProjectiveOptimum
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import Reg.Support.DependentFamily

/-! A source-bound observation of support families at each field and class count. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open CPECCBridge CPECCBridge.ProjectiveOptimum

namespace Reg.D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ProjectiveOptimum

universe u

noncomputable section

private abbrev Family (F : Type u) (s : ℕ) :=
  Fin s → Finset (Finset (Fin (Nat.card F * (Nat.card F + 1) + 2)))

abbrev signature : Signature.{u + 1, 0, 0, 0, 0} where
  Params := (_ : Type u) × ℕ
  State p := Family p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Family p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ P => P) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena.{u + 1, 0, 0, 0, 0} where
  signature := signature
  Law R := ∀ (F : Type u) [Field F] [Finite F],
    7 ≤ Nat.card F → Odd (Nat.card F) →
    (let q := Nat.card F
     let n := q * (q + 1) + 2
     let m := n / 2
     (Odd m ∧ ¬ IsSquare (q + 1)) ∨ (Even m ∧ ¬ IsSquare (q - 1))) →
    let q := Nat.card F
    let n := q * (q + 1) + 2
    IsGreatest {s : ℕ | ∃ P : Fin s → Finset (Finset (Fin n)),
      IsSupportFamily (R.readout () ⟨F, s⟩ P) (q - 1) 2} (n - 1)

private local instance primeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem card_seven : Nat.card (ULift.{u} (ZMod 7)) = 7 := by
  rw [Nat.card_ulift, Nat.card_eq_fintype_card, ZMod.card]

private theorem seven_obstruction : (Odd 29 ∧ ¬ IsSquare (8 : ℕ)) ∨
    (Even 29 ∧ ¬ IsSquare (6 : ℕ)) := by
  refine Or.inl ⟨⟨14, rfl⟩, ?_⟩
  rintro ⟨a, ha⟩
  rcases le_or_gt a 2 with h | h
  · have := Nat.mul_le_mul h h
    omega
  · have hle : 3 ≤ a := by omega
    have := Nat.mul_le_mul hle hle
    omega

private theorem empty_invalid {n s w : ℕ} (hn : 2 ≤ n) (hs : 0 < s) :
    ¬ IsSupportFamily (fun _ : Fin s => (∅ : Finset (Finset (Fin n)))) w 2 := by
  intro h
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := fun he => by simpa [a, b] using congrArg Fin.val he
  obtain ⟨A, hA, _⟩ := h.2.1 ⟨0, hs⟩ {a, b} (by simp [hab])
  simp at hA

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let F := ULift.{u} (ZMod 7)
  have hbad := h F (by rw [card_seven]) (by rw [card_seven]; decide)
    (by dsimp [F]; rw [card_seven]; exact seven_obstruction)
  obtain ⟨_, hEmpty⟩ := hbad.1
  let n := Nat.card F * (Nat.card F + 1) + 2
  change IsSupportFamily (fun _ : Fin (n - 1) => (∅ : Finset (Finset (Fin n))))
    (Nat.card F - 1) 2 at hEmpty
  exact empty_invalid (by dsimp [n]; omega) (by dsimp [n]; omega) hEmpty

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let F := ULift.{u} (ZMod 7)
  have h := support_optimum F (by rw [card_seven]) (by rw [card_seven]; decide)
    (by dsimp [F]; rw [card_seven]; exact seven_obstruction)
  obtain ⟨P, hP⟩ := h.1
  refine ⟨⟨F, Nat.card F * (Nat.card F + 1) + 2 - 1⟩, P, fun _ => ∅, ?_⟩
  change P ≠ fun _ => ∅
  intro he
  rw [he] at hP
  exact empty_invalid (by omega) (by omega) hP

def source_registration : Registration arena.{u} (type_of% (@support_optimum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨support_optimum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (@Subsingleton.elim Unit _ j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@support_optimum.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ProjectiveOptimum.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ProjectiveOptimum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ProjectiveOptimum
    definition := none
    coordinates := #[0, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "body", "fn", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Combinatorics.Hamming.ConstantPowerCooling.ProjectiveOptimum
