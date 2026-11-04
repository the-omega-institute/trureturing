import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible
import Reg.Support.DependentFamily

/-! Typed four-slot registration attempt for the settling theorem. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible
open _root_.D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible

structure Input where
  p : ℕ
  q : ℕ
  f : ℤ × ℤ → T
  k : ℕ

abbrev signature : Signature where
  Params := Input
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev rootExists (i : Input) : Prop :=
  ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ ∃ g : ℤ × ℤ → T,
    IsSandpile (m * i.p) (n * i.q) g ∧ i.k • g = embed i.p i.q m n i.f

def actual : Realization signature :=
  realize signature (fun _ i b => b = true ∧ rootExists i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ i : Input, 1 ≤ i.p → 1 ≤ i.q → IsSandpile i.p i.q i.f → 1 ≤ i.k → R.readout () i true

theorem bridge :
    _root_.D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.claim ↔
      arena.Law actual := by
  constructor
  · intro h i hp hq hf hk
    dsimp [actual, realize]
    exact ⟨rfl, h i.p i.q hp hq i.f hf i.k hk⟩
  · intro h p q hp hq f hf k hk
    dsimp [actual, realize] at h
    exact (h ⟨p, q, f, k⟩ hp hq hf hk).2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let f : ℤ × ℤ → T := fun _ => 0
  have hf : IsSandpile 2 2 f := by
    constructor
    · intro z hz
      rfl
    · intro z hz
      simp [f]
  have hh := h { p := 2, q := 2, f := f, k := 1 } (by decide) (by decide) hf (by decide)
  simpa [rejected, realize] using hh

theorem dependence : ObservationalDependence signature actual := by
  intro ⟨⟩
  let f0 : ℤ × ℤ → T := fun _ => 0
  let i0 : Input := ⟨2, 2, f0, 1⟩
  have h0 : rootExists i0 := by
    exact (_root_.D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.result
      2 2 (by omega) (by omega) f0 (by
        constructor
        · intro z hz
          rfl
        · intro z hz
          simp [f0]) 1 (by omega))
  refine ⟨i0, true, false, ?_⟩
  intro hEq
  have hleft : actual.readout () i0 true := by
    dsimp [actual, realize]
    exact ⟨rfl, h0⟩
  have hfalse : actual.readout () i0 false := Eq.mp hEq hleft
  simpa [actual, realize] using hfalse

def registration : Registration arena
    (_root_.D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.claim) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp _root_.D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.result)
      (type_of% (realize signature (fun _ i b => b = true ∧ rootExists i) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.result.information_unit,
  realizationName := `Reg.D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ i b => b = true ∧ rootExists i) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.StatisticalMechanics.Sandpiles.ShkolnikovSandpileLimitDivisible
