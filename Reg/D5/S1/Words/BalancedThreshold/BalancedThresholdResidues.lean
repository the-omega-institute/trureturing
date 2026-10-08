/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdResidues
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdResidues
   mirror-E: none(waiver:source-bound-denominator-orbit)
   anchors: []
   utility: none
   digest: A source-bound family registers the infinite denominator residue invariant. -/

import D5.S1.Words.BalancedThreshold.BalancedThresholdResidues
import Reg.Support.DependentFamily

open D5.S1.Words.BalancedThreshold
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdResidues
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
  Law R := ∀ t : ℕ, 5 ≤ t →
    let g := R.readout () () (uniformSlope t / (1 - uniformSlope t))
    ∀ n, 1 ≤ n →
      (⌊g.dens n⌋ : ℝ) = g.dens n ∧
      ⌊g.dens n⌋ ≡
        (if n % 8 = 1 then 2 else if n % 8 = 2 then 1
          else if n % 8 = 3 then 0 else if n % 8 = 4 then 1
          else if n % 8 = 5 then -2 else if n % 8 = 6 then -1
          else if n % 8 = 7 then 0 else -1 : ℤ) [ZMOD (t : ℤ)] ∧
      ⌊g.dens n⌋ ≡ (if n % 2 = 0 then 0 else 1 : ℤ) [ZMOD (t : ℤ) + 1]

def bad : Realization signature :=
  realize signature (fun _ _ _ => ⟨0, Stream'.Seq.nil⟩) (fun e => nomatch e)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨uniform_denominator_residues, bad, ?_⟩
    intro h
    have hf := (h 5 (by norm_num) 1 (by norm_num)).2.1
    norm_num [bad, realize, GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux,
      GenContFract.contsAux, Int.ModEq] at hf
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hf := (h 5 (by norm_num) 1 (by norm_num)).2.1
      norm_num [bad, realize, GenContFract.den_eq_conts_b,
        GenContFract.nth_cont_eq_succ_nth_contAux,
        GenContFract.contsAux, Int.ModEq] at hf
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let theta := uniformSlope 5 / (1 - uniformSlope 5)
    refine ⟨(), 0, theta, ?_⟩
    intro heq
    have hden := congrArg (fun g : GenContFract ℝ => g.dens 1) heq
    change (GenContFract.of (0 : ℝ)).dens 1 = (GenContFract.of theta).dens 1 at hden
    have ht := GenContFract.first_den_eq ((uniform_ratio_expansion 5 (by norm_num)).2 0)
    have hz : (GenContFract.of (0 : ℝ)).s = Stream'.Seq.nil := by
      simpa using GenContFract.of_s_of_int ℝ 0
    have hd0 : (GenContFract.of (0 : ℝ)).dens 1 = 1 := by
      norm_num [GenContFract.den_eq_conts_b,
        GenContFract.nth_cont_eq_succ_nth_contAux, GenContFract.contsAux, hz]
    change (GenContFract.of theta).dens 1 = (7 : ℝ) at ht
    rw [hd0, ht] at hden
    norm_num at hden

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.BalancedThreshold.BalancedThresholdResidues
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "value", "fn"], functionOperand := true }] }

register_information_theorem uniform_denominator_residues in arena
  readout via (realize signature (fun _ _ x => GenContFract.of x) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.BalancedThreshold.BalancedThresholdResidues
