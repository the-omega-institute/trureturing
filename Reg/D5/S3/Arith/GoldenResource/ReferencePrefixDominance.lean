import D5.S3.Arith.GoldenResource.ReferencePrefixDominance
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance

open Finset
open _root_.D5.S3.Arith.GoldenResource.ReferencePrefixDominance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Only the harmonic summand varies; the complete source
telescope and geometric-prefix logarithm remain in the law. -/
abbrev arena : Arena where
  signature := signature
  Law := fun r => ∀ {z : ℝ} {a : ℕ},
    1 ≤ a → 0 < z → z < 1 →
    Real.log (∑ k ∈ range (a + 1), z ^ k) <
      ∑ k ∈ range a, r.readout () ⟨z, a⟩ k

def actual : Realization signature :=
  realize signature (fun _ p k => p.1 ^ (k + 1) / (k + 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0)
    (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h (z := (1 / 2 : ℝ)) (a := 1)
    (by decide) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hfalse
  exact (not_lt_of_ge (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)).le) hfalse

def registration : Registration arena
    (∀ {z : ℝ} {a : ℕ}, 1 ≤ a → 0 < z → z < 1 →
      Real.log (∑ k ∈ range (a + 1), z ^ k) <
        ∑ k ∈ range a, z ^ (k + 1) / (k + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨log_geom_prefix_lt_harmonic_prefix, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨(1 / 2 : ℝ), 2⟩, 0, 1, ?_⟩
    norm_num [actual, realize]

register_information_theorem log_geom_prefix_lt_harmonic_prefix in arena
  readout via (realize signature
    (fun _ p k => p.1 ^ (k + 1) / (k + 1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.GoldenResource.ReferencePrefixDominance
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      functionOperand := true }] })
  escape continues (open)

#print axioms registration

end

end Reg.D5.S3.Arith.GoldenResource.ReferencePrefixDominance
