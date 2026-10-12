import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Shadowing.StoneanForwardTubeObstruction
import Reg.Support.DependentFamily

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S1.Dynamics.Shadowing
open TopologicalSpace Set

namespace Reg.D5.S1.Dynamics.Shadowing.StoneanForwardTubeObstruction

noncomputable section
universe u

abbrev sourceParameters := Σ Y : Type u, Y → Y

abbrev signature : Signature where
  Params := sourceParameters.{u}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ x => Classical.choice ⟨x⟩) (fun e => nomatch e)

/-- The complete theorem telescope is retained; only the dynamics in its
conclusion varies. The hypotheses continue to refer to the prescribed map. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Y : Type u} [TopologicalSpace Y] [ExtremallyDisconnected Y]
    (g : Y → Y) (_hg : Continuous g) (U : ℕ → Set Y)
    (_hU : ∀ n, IsOpen (U n))
    (_hdis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (_hne : (U 0).Nonempty) (_hforward : ∀ n, MapsTo g (U n) (U (n + 1))),
    ¬ HasShadowing (fun x => R.readout () ⟨Y, g⟩ x)

private theorem constant_shadows_discrete {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology Y] (c : Y) : HasShadowing (fun _ : Y => c) := by
  classical
  intro C hC
  let A : Opens Y := ⟨{c}, isOpen_discrete _⟩
  let B : Opens Y := ⟨{c}ᶜ, isOpen_discrete _⟩
  let D : Finset (Opens Y) := {A, B}
  have hD : IsOpenCover (fun U : D => U.1) := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    by_cases hx : x = c
    · exact Opens.mem_iSup.mpr ⟨⟨A, by simp [D]⟩, hx⟩
    · exact Opens.mem_iSup.mpr ⟨⟨B, by simp [D]⟩, hx⟩
  refine ⟨D, hD, fun x hx => ⟨x 0, fun n => ?_⟩⟩
  cases n with
  | zero =>
    obtain ⟨U, hU⟩ := hC.exists_mem (x 0)
    exact ⟨U.1, U.2, hU, hU⟩
  | succ n =>
    obtain ⟨U, hUD, hcU, hxU⟩ := hx n
    have hxn : x (n + 1) = c := by
      have hU : U = A ∨ U = B := by simpa [D] using hUD
      rcases hU with rfl | rfl
      · exact hxU
      · exact False.elim (hcU rfl)
    obtain ⟨V, hV⟩ := hC.exists_mem c
    refine ⟨V.1, V.2, ?_, ?_⟩
    · simpa only [Function.iterate_succ_apply', Function.comp_apply] using hV
    · simpa [hxn] using hV

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Y := ULift.{u} ℕ
  letI : TopologicalSpace Y := ⊥
  letI : DiscreteTopology Y := ⟨rfl⟩
  letI : ExtremallyDisconnected Y := ⟨fun _ _ => isOpen_discrete _⟩
  let g : Y → Y := fun x => ⟨x.down + 1⟩
  let U : ℕ → Set Y := fun n => {⟨n⟩}
  have hdis : ∀ i j, i ≠ j → Disjoint (U i) (U j) := by
    intro i j hij
    simp only [U, disjoint_singleton]
    exact fun he => hij (congrArg ULift.down he)
  have hf : ∀ n, MapsTo g (U n) (U (n + 1)) := by
    intro n x hx
    simp only [U, mem_singleton_iff] at hx ⊢
    subst x
    rfl
  have hh := h g continuous_of_discreteTopology U (fun _ => isOpen_discrete _)
    hdis ⟨⟨0⟩, rfl⟩ hf
  change ¬ HasShadowing (fun _ : Y => Classical.choice (inferInstance : Nonempty Y)) at hh
  exact hh (constant_shadows_discrete _)

def registration : Registration arena.{u}
    (type_of% (@not_has_shadowing_of_disjoint_open_forward_tubes.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@not_has_shadowing_of_disjoint_open_forward_tubes.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let Y := ULift.{u} ℕ
    let p : sourceParameters.{u} := ⟨Y, fun x => ⟨x.down + 1⟩⟩
    refine ⟨p, (⟨0⟩ : Y), (⟨1⟩ : Y), ?_⟩
    change (⟨1⟩ : Y) ≠ ⟨2⟩
    exact fun he => by
      have hn : (1 : ℕ) = 2 := congrArg ULift.down he
      norm_num at hn

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@not_has_shadowing_of_disjoint_open_forward_tubes.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.StoneanForwardTubeObstruction.forwardTubes
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.StoneanForwardTubeObstruction.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Shadowing.StoneanForwardTubeObstruction
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms registration_1

end
end Reg.D5.S1.Dynamics.Shadowing.StoneanForwardTubeObstruction
