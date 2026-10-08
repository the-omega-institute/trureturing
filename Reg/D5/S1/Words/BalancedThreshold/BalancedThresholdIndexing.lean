/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdIndexing
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdIndexing
   mirror-E: none(waiver:source-bound-computed-digit)
   anchors: []
   utility: none
   digest: Unimodular indexing is registered at the integral digit realized in the real stream. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdIndexing
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold GenContFract
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdIndexing
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ c => (c : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {theta : ℝ}, 0 < theta → theta < 1 → Irrational theta →
    ∀ p q r s : ℕ, (p * s + 1 = r * q ∨ r * q + 1 = p * s) →
    ((p : ℝ) - theta * q) * ((r : ℝ) - theta * s) < 0 →
    let g := GenContFract.of theta
    ∃ N m : ℕ, ∃ c : ℤ, g.s.get? N = some ⟨1, R.readout () () c⟩ ∧ (m : ℤ) < c ∧
      let v := g.contsAux (N + 1)
      let w := g.contsAux N
      let z : Pair ℝ := ⟨(m : ℝ) * v.a + w.a, (m : ℝ) * v.b + w.b⟩
      (⟨(p : ℝ), (q : ℝ)⟩ = v ∧ ⟨(r : ℝ), (s : ℝ)⟩ = z) ∨
      (⟨(r : ℝ), (s : ℝ)⟩ = v ∧ ⟨(p : ℝ), (q : ℝ)⟩ = z)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨@unimodular_bracket_continuants, bad, ?_⟩
    intro h
    let theta := Real.sqrt 2 - 1
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    have ht0 : 0 < theta := by dsimp [theta]; nlinarith
    have ht1 : theta < 1 := by dsimp [theta]; nlinarith
    have hti : Irrational theta := by
      simpa [theta] using irrational_sqrt_two.sub_ratCast 1
    obtain ⟨N, m, c, hdigit, _, _⟩ := h ht0 ht1 hti 0 1 1 0
      (Or.inl (by norm_num)) (by norm_num; exact ht0)
    change (GenContFract.of theta).s.get? N = some ⟨1, (0 : ℝ)⟩ at hdigit
    have impossible := GenContFract.of_one_le_get?_partDen
      (GenContFract.partDen_eq_s_b hdigit)
    norm_num at impossible
  sensitivity := by
    have refute : ¬ arena.Law bad := by
      intro h
      let theta := Real.sqrt 2 - 1
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hs0 := Real.sqrt_nonneg (2 : ℝ)
      have ht0 : 0 < theta := by dsimp [theta]; nlinarith
      have ht1 : theta < 1 := by dsimp [theta]; nlinarith
      have hti : Irrational theta := by
        simpa [theta] using irrational_sqrt_two.sub_ratCast 1
      obtain ⟨N, m, c, hdigit, _, _⟩ := h ht0 ht1 hti 0 1 1 0
        (Or.inl (by norm_num)) (by norm_num; exact ht0)
      change (GenContFract.of theta).s.get? N = some ⟨1, (0 : ℝ)⟩ at hdigit
      have impossible := GenContFract.of_one_le_get?_partDen
        (GenContFract.partDen_eq_s_b hdigit)
      norm_num at impossible
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, refute⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdIndexing
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
      "fn", "arg", "arg", "arg", "arg", "fn"]
    functionOperand := true }] }

register_information_theorem unimodular_bracket_continuants in arena
  readout via
    (realize signature (fun _ _ c => (c : ℝ)) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdIndexing
