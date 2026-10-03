import D5.S3.Geometry.Polygons.BalancedPlanarClosure
import Reg.Support.DependentFamily

open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Polygons.BalancedPlanarClosure
noncomputable section

/-- The selected observation is the actual resultant of a configuration. -/
abbrev signature : Signature where
  Params := ℕ
  State m := Fin m → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => ∑ i, v i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Preserve every source binder, hypothesis, norm condition, and existential witness.
Only the final sum observation is varied. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ) (L : Fin m → ℝ), (∀ i, 0 ≤ L i) →
    (∀ i, 2 * L i ≤ ∑ j, L j) →
    ∃ v : Fin m → ℂ, (∀ i, ‖v i‖ = L i) ∧ R.readout () m v = 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨v, _, hv⟩ := h 0 Fin.elim0 (by simp) (by simp)
  exact one_ne_zero hv

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Geometry.Polygons.BalancedPlanarClosure.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    simp [actual, realize]

register_information_theorem _root_.D5.S3.Geometry.Polygons.BalancedPlanarClosure.result in arena
  readout via (realize signature (fun _ _ v => ∑ i, v i) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Geometry.Polygons.BalancedPlanarClosure
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration
end
end Reg.D5.S3.Geometry.Polygons.BalancedPlanarClosure
