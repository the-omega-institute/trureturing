/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeHallCoding
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeHallCoding
   mirror-E: none(waiver:four-digit-binary-hall-coding)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A source-bound readout registers the binary coding of every C4 expansion. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallCoding
import Reg.Support.DependentFamily
import Mathlib.Tactic

open D5.S1.Words.KAbelianLagrange
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallCoding
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => GenContFract ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => GenContFract.of x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, x ∈ hallCantor → ∃ b : ℕ → Bool, ∀ n : ℕ,
    (∀ i : ℕ, ∀ hi : i < (hallBinaryAddress b n).1.length,
      (R.readout () () x).s.get? i =
        some ⟨1, (((hallBinaryAddress b n).1[i]).val + 1 : ℕ)⟩) ∧
    ∃ a : ℕ, (hallBinaryAddress b n).2.val + 1 ≤ a ∧ a ≤ 4 ∧
      (GenContFract.of x).s.get? (hallBinaryAddress b n).1.length =
        some ⟨1, (a : ℝ)⟩

def bad : Realization signature :=
  realize signature (fun _ _ _ => ⟨0, Stream'.Seq.nil⟩) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨hall_cantor_binary_coding, bad, ?_⟩
    intro h
    obtain ⟨b, hb⟩ := h _ hall_cantor_hull.2.1
    obtain ⟨_, _, ht⟩ := hall_binary_branch_expansion b
    have hj := (hallBinaryAddress b 3).2.isLt
    have hp := (ht 3).1
    have hi : 0 < (hallBinaryAddress b 3).1.length := by omega
    have hget := (hb 3).1 0 hi
    simp [bad, realize] at hget
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      obtain ⟨b, hb⟩ := h _ hall_cantor_hull.2.1
      obtain ⟨_, _, ht⟩ := hall_binary_branch_expansion b
      have hj := (hallBinaryAddress b 3).2.isLt
      have hp := (ht 3).1
      have hi : 0 < (hallBinaryAddress b 3).1.length := by omega
      have hget := (hb 3).1 0 hi
      simp [bad, realize] at hget
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, (Real.sqrt 2 - 1) / 2, ?_⟩
    intro heq
    obtain ⟨a, _, _, ha⟩ := hall_cantor_hull.2.1.2.2.2 0
    have hget := congrArg (fun g : GenContFract ℝ => g.s.get? 0) heq
    change (GenContFract.of (0 : ℝ)).s.get? 0 =
      (GenContFract.of ((Real.sqrt 2 - 1) / 2)).s.get? 0 at hget
    rw [ha] at hget
    have hz : (GenContFract.of (0 : ℝ)).s = Stream'.Seq.nil := by
      simpa using GenContFract.of_s_of_int ℝ 0
    simp [hz] at hget

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallCoding
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "arg", "body", "body", "fn", "arg",
    "body", "body", "fn", "arg", "fn", "arg", "arg", "fn"], functionOperand := true }] }

register_information_theorem hall_cantor_binary_coding in arena
  readout via (realize signature (fun _ _ x => GenContFract.of x) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeHallCoding
