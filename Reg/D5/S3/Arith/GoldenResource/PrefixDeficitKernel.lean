import D5.S3.Arith.GoldenResource.PrefixDeficitKernel
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel

open Real Set MeasureTheory
open _root_.D5.S3.Arith.GoldenResource.PrefixDeficitKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The deficit is the observation; the original kernel and all hypotheses remain fixed. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (a : ℕ) (z : ℝ), 1 ≤ a → 0 < z → z < 1 →
    IntervalIntegrable (fun t : ℝ => t ^ a * P a t / S a t) volume 0 z ∧
    r.readout () a z = (∫ t in (0 : ℝ)..z, t ^ a * P a t / S a t) ∧
    (a : ℝ) * z ^ (a + 1) / (((a : ℝ) + 1) * (1 + z)) ≤ r.readout () a z ∧
    r.readout () a z ≤ (a : ℝ) * z ^ (a + 1) / ((a : ℝ) + 1)

def actual : Realization signature :=
  realize signature (fun _ a z => D a z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 (1 / 2) (by decide) (by norm_num) (by norm_num)).2.2.1
  norm_num [rejected, realize] at hh

def registration : Registration arena
    (∀ (a : ℕ) (z : ℝ), 1 ≤ a → 0 < z → z < 1 →
      IntervalIntegrable (fun t : ℝ => t ^ a * P a t / S a t) volume 0 z ∧
      D a z = (∫ t in (0 : ℝ)..z, t ^ a * P a t / S a t) ∧
      (a : ℝ) * z ^ (a + 1) / (((a : ℝ) + 1) * (1 + z)) ≤ D a z ∧
      D a z ≤ (a : ℝ) * z ^ (a + 1) / ((a : ℝ) + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, 0, 1 / 2, ?_⟩
    change D 1 0 ≠ D 1 (1 / 2)
    have hzero : D 1 0 = 0 := by simp [D, Q, S]
    rw [hzero]
    have hh := (result 1 (1 / 2) (by decide) (by norm_num) (by norm_num)).2.2.1
    norm_num at hh
    exact ne_of_lt (by linarith)

register_information_theorem result in arena
  readout via (realize signature (fun _ a z => D a z) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.GoldenResource.PrefixDeficitKernel
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration

end

end Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel
