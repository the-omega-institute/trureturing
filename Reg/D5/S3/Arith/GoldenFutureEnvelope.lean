import D5.S3.Arith.GoldenFutureEnvelope
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.GoldenFutureEnvelope

open _root_.D5.S3.Arith.GoldenFutureEnvelope
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.GoldenFutureExtensionMaximum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law := fun r => ∀ {lambda : ℝ}, 0 < lambda →
    (∀ n : ℕ, 1 ≤ n → goldenResourceObjective lambda n ≤ r.readout () lambda n) ∧
    (∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n →
      r.readout () lambda (p * n) ≤ r.readout () lambda n) ∧
    (∀ U : ℕ → ℝ,
      (∀ n : ℕ, 1 ≤ n → goldenResourceObjective lambda n ≤ U n) →
      (∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n → U (p * n) ≤ U n) →
      ∀ n : ℕ, 1 ≤ n → r.readout () lambda n ≤ U n)

def actual : Realization signature :=
  realize signature (fun _ lambda n => goldenFutureEnvelope lambda n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (lambda := 1) (by norm_num)).1 1 (by norm_num)
  norm_num [rejected, realize, goldenResourceObjective] at hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_future_envelope_least, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    have hzero : goldenFutureEnvelope (1 / 25) 0 = 0 := by
      have hempty : {m : ℕ | 0 ∣ m ∧ 1 ≤ m} = ∅ := by
        ext m
        simp
      rw [goldenFutureEnvelope, hempty, Set.image_empty, Real.sSup_empty]
    have hJone : goldenResourceObjective (1 / 25) 1 = 0 := by
      simp [goldenResourceObjective]
    have hpositive : 0 < goldenResourceObjective (1 / 25) 5040 := by
      obtain ⟨hle, heq⟩ := golden_resource_unique_optimum (n := 1) (by norm_num)
      rw [hJone] at hle heq
      by_contra h
      have hz : 0 = goldenResourceObjective (1 / 25) 5040 := by linarith
      norm_num at heq
      exact heq hz
    obtain ⟨m, hdiv, hm, hmax⟩ :=
      golden_future_extension_maximum_attained (by norm_num : (0 : ℝ) < 1 / 25)
        (n := 1) (by norm_num)
    have hg : IsGreatest
        (goldenResourceObjective (1 / 25) '' {k : ℕ | 1 ∣ k ∧ 1 ≤ k})
        (goldenResourceObjective (1 / 25) m) := by
      refine ⟨⟨m, ⟨hdiv, hm⟩, rfl⟩, ?_⟩
      rintro _ ⟨k, hk, rfl⟩
      exact (sub_le_sub_iff_right _).mp (hmax k hk.1 hk.2)
    have hlower : goldenResourceObjective (1 / 25) 5040 ≤ goldenFutureEnvelope (1 / 25) 1 :=
      le_csSup hg.bddAbove ⟨5040, ⟨one_dvd _, by norm_num⟩, rfl⟩
    refine ⟨1 / 25, 0, 1, ?_⟩
    change goldenFutureEnvelope (1 / 25) 0 ≠ goldenFutureEnvelope (1 / 25) 1
    rw [hzero]
    exact ne_of_lt (hpositive.trans_le hlower)

register_information_theorem golden_future_envelope_least in arena
  readout via (realize signature
    (fun _ lambda n => goldenFutureEnvelope lambda n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.GoldenFutureEnvelope
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "arg", "fn"]
      functionOperand := true }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Arith.GoldenFutureEnvelope
