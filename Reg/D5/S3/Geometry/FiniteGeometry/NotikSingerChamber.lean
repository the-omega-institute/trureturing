import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.FiniteGeometry.NotikSingerChamber
import Reg.Support.DependentFamily

/-! Source-bound registration for the pointwise conclusion of the chamber theorem. -/

namespace Reg.D5.S3.Geometry.FiniteGeometry.NotikSingerChamber

open _root_.D5.S3.Geometry.FiniteGeometry.NotikSingerChamber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature where
  Params := Σ m : ℕ, Fin (m + 1) → ℕ
  State p := Fin (p.1 + 1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p i => p.2 i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Vary the reference mark readout in the pointwise uniqueness conclusion. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {m : ℕ} {x : Fin (m + 1) → ℕ} {G : ℕ}
    (_hm : 0 < m) (_hzero : x 0 = 0) (_hx : StrictMono x) (_hG : 0 < G)
    (_hgap : ∀ i : Fin m, x i.succ - x i.castSucc ≤ G)
    (_hperfect : CyclicPerfectDifference x (x (Fin.last m) + G)),
    (∀ i j k l : Fin (m + 1), i < j → k < l → x j - x i = x l - x k → (i, j) = (k, l)) ∧
    Chamber x (fun i => (x i : ℝ)) ∧
      ∀ y : Fin (m + 1) → ℝ, Chamber x y → y (Fin.last m) ≤ (x (Fin.last m) : ℝ) →
        ∀ i : Fin (m + 1), y i = (r.readout () ⟨m, x⟩ i : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have perfect : CyclicPerfectDifference (m := 1) Fin.val 3 := by
    intro d hd hdN
    have hd' : d = 1 ∨ d = 2 := by omega
    rcases hd' with rfl | rfl
    · exact ⟨(0, 1), by decide, by decide⟩
    · exact ⟨(1, 0), by decide, by decide⟩
  have hbad := h (m := 1) (x := Fin.val) (G := 2) (by decide) rfl
    (fun _ _ hlt => hlt) (by decide) (by decide) perfect
  have hzero := hbad.2.2 _ hbad.2.1 le_rfl 0
  simpa [rejected, realize] using hzero

def evidence : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨⟨1, Fin.val⟩, 0, 1, by decide⟩

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Geometry.FiniteGeometry.NotikSingerChamber.result.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteGeometry.NotikSingerChamber.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p i => p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteGeometry.NotikSingerChamber
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Geometry.FiniteGeometry.NotikSingerChamber
