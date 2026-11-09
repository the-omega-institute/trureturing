import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Dynamics.Shadowing.CompactPseudoOrbitSelector

/-! Observe the actual tracing distance. The full source telescope and both
global and limit conclusions are retained. The typed logical bridge does not
provide a source-selection certificate. -/

noncomputable section
open Set Filter Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Dynamics.Shadowing.CompactSelector

namespace Reg.D5.S1.Dynamics.Shadowing.CompactPseudoOrbitSelector
universe u

abbrev distanceSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization distanceSignature :=
  realize distanceSignature (fun _ _ r => r) (fun e => nomatch e)

def rejected : Realization distanceSignature :=
  realize distanceSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := distanceSignature
  Law A := ∀ {M : Type u} [MetricSpace M] (f : M ≃ₜ M) [CompactSpace M]
    {δ : ℝ} (hδ : 0 < δ) (Q : Space f δ → M), Continuous Q →
    (∀ p, Q (trueOrbit f hδ.le p) = p) →
    (∀ x, Q (shift f 1 x) = f (Q x)) →
    (∀ ε > 0, ∃ γ > 0, ∃ hγδ : γ ≤ δ, ∀ (x : Space f γ) (k : ℤ),
      A.readout () () (dist (orbit f (Q (inclusion f hγδ x)) k) (x.1 k)) < ε) ∧
    (∀ x : Space f δ, Tendsto (linkError f x.1) cofinite (𝓝 0) →
      (∀ ε > 0, ∃ N : ℕ, ∀ k : ℤ, N ≤ k.natAbs →
        dist (orbit f (Q x) k) (x.1 k) < ε) ∧
      Tendsto (fun k : ℤ => dist (orbit f (Q x) k) (x.1 k)) cofinite (𝓝 0))

theorem actual_law : arena.{u}.Law actual := by
  simpa only [arena, actual, realize] using (@global_and_limit_shadowing.{u})

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  let f := Homeomorph.refl PUnit.{u + 1}
  let Q : Space f 1 → PUnit.{u + 1} := fun _ => PUnit.unit
  have h := (hh f (by norm_num : (0 : ℝ) < 1) Q continuous_const
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)).1
  obtain ⟨γ, hγ, hγδ, htrace⟩ := h (1 / 2) (by norm_num)
  have hbad := htrace (trueOrbit f hγ.le PUnit.unit) 0
  norm_num [rejected, realize] at hbad

def familyRegistration : Registration arena.{u} (type_of% (@global_and_limit_shadowing.{u})) where
  actual := actual
  bridge := by simp only [arena, actual, realize]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@global_and_limit_shadowing.{u}) (Realization distanceSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Shadowing.CompactPseudoOrbitSelector.globalAndLimitTracing
  realizationName := `Reg.D5.S1.Dynamics.Shadowing.CompactPseudoOrbitSelector.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize distanceSignature (fun _ _ r => r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Dynamics.Shadowing.CompactPseudoOrbitSelector
