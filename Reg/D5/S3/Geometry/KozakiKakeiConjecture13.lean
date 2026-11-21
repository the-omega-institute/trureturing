import D5.S3.Geometry.KozakiKakeiConjecture13
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Readouts of dihedral membership and of the written level on the permutation fibers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Geometry.KozakiKakeiConjecture13

open _root_.D5.S3.Geometry.KozakiKakei
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit

noncomputable section
open Classical

private theorem identity_dihedral : Dihedral (Equiv.refl (Col 2)) :=
  ⟨0, Or.inl (fun i => (zero_add i).symm)⟩

private theorem swap_not_dihedral : ¬ Dihedral (Equiv.swap (0 : Col 2) 1) := by
  rintro ⟨a, h | h⟩
  · have ha : a = 1 := by simpa using (h 0).symm
    have h1 := h 1
    rw [ha] at h1
    exact (by decide : (0 : Col 2) ≠ 1 + 1) (by simpa using h1)
  · have ha : a = 1 := by simpa using (h 0).symm
    have h2 := h 2
    rw [ha] at h2
    have hswap : Equiv.swap (0 : Col 2) 1 2 = 2 :=
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    rw [hswap] at h2
    exact (by decide : (2 : Col 2) ≠ 1 - 2) h2

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun m => Equiv.Perm (Col m)) (fun _ => Bool)

private def actual : Realization signature :=
  realize signature (fun _ _ σ => decide (Dihedral σ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (_ : m ≠ 3) (σ : Equiv.Perm (Col m)),
    Allowable hm σ ↔ R.readout () m σ = true

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have ha := (conjecture_13 (m := 2) (by decide) (by decide) (Equiv.refl _)).mpr
    identity_dihedral
  have impossible := (h (by decide) (by decide) (Equiv.refl (Col 2))).mp ha
  cases impossible

def evidence : Registration arena (type_of% @conjecture_13) where
  actual := actual
  bridge := by
    simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using @conjecture_13,
    rejected, rejected_fails⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_fails
  dependence := by
    intro _
    refine ⟨2, Equiv.refl _, Equiv.swap 0 1, ?_⟩
    simpa [actual, realize, identity_dihedral, swap_not_dihedral]

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@conjecture_13) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.KozakiKakei.conjecture_13.__information_unit
  realizationName := `Reg.D5.S3.Geometry.KozakiKakeiConjecture13.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ σ => decide (Dihedral σ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.KozakiKakeiConjecture13
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Level

private def observesLevel : Realization signature :=
  realize signature (fun _ _ σ => decide (PreservesLevel σ)) (fun e => nomatch e)

private abbrev levelArena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ} (hm : 2 ≤ m) (σ : Equiv.Perm (Col m)),
    Allowable hm σ ↔ R.readout () m σ = true

private theorem identity_preserves : PreservesLevel (Equiv.refl (Col 2)) :=
  fun _ _ h => h

private theorem rejects_level : ¬ levelArena.Law rejected := by
  intro h
  have ha := (allowable_iff_preservesLevel (m := 2) (by decide) (Equiv.refl _)).mpr
    identity_preserves
  have impossible := (h (by decide) (Equiv.refl (Col 2))).mp ha
  cases impossible

def levelEvidence : Registration levelArena (type_of% @allowable_iff_preservesLevel) where
  actual := observesLevel
  bridge := by
    simp [levelArena, observesLevel, realize]
  variation := ⟨by simpa [levelArena, observesLevel, realize] using @allowable_iff_preservesLevel,
    rejected, rejects_level⟩
  sensitivity := sensitivity levelArena.Law observesLevel rejected rejects_level
  dependence := by
    intro _
    refine ⟨2, Equiv.refl _, Equiv.swap 0 1, ?_⟩
    have bad : ¬ PreservesLevel (Equiv.swap (0 : Col 2) 1) := by
      intro hp
      have ha := (allowable_iff_preservesLevel (m := 2) (by decide) _).mpr hp
      exact swap_not_dihedral ((conjecture_13 (m := 2) (by decide) (by decide) _).mp ha)
    simpa [observesLevel, realize, identity_preserves, bad]

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@allowable_iff_preservesLevel) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.KozakiKakei.allowable_iff_preservesLevel.__information_unit
  realizationName := `Reg.D5.S3.Geometry.KozakiKakeiConjecture13.Level.levelEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨levelArena⟩
  objectArena := .source ⟨levelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source levelArena ⟨levelEvidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ σ => decide (PreservesLevel σ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.KozakiKakeiConjecture13
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Level

end

end Reg.D5.S3.Geometry.KozakiKakeiConjecture13
