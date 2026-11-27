/- GID: D5/S3/Quantum/PureState/JointRecordDecodingCrossover
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/JointRecordDecodingCrossover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint POVMs attain the finite-scale crossover on varying product carriers. -/

import D5.S3.Quantum.PureState.BinaryPureRecordDecoding
import D5.S3.Quantum.PureState.PureRecordDecodingThreshold

/-! The finite-scale limit of the optimum and its realization by joint POVMs. -/

namespace JointRecordDecoding

noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder Topology
open D5.S3.Quantum.Subentropy.GuessingProbability

/-- Finite-scale crossover for the actual optimum on a sequence of original record carriers.
The carrier may vary with the sequence index. -/
theorem pGuess_productRecord_crossover
    (A : ℕ → Type*) [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
    (v : ∀ n, Bool → A n → ℂ)
    (hv : ∀ n b, star (v n b) ⬝ᵥ v n b = 1) (copies : ℕ → ℕ) (scale : ℝ)
    (hzero : Tendsto (fun n => ‖star (v n false) ⬝ᵥ v n true‖ ^ 2) atTop (𝓝 0))
    (hne : ∀ᶠ n in atTop, ‖star (v n false) ⬝ᵥ v n true‖ ^ 2 ≠ 0)
    (hscale : Tendsto (fun n => (copies n : ℝ) * ‖star (v n false) ⬝ᵥ v n true‖ ^ 2)
      atTop (𝓝 scale)) :
    Tendsto (fun n => pGuess (uniformPrior (Word (copies n)))
      (productRecordState (v n) (hv n))) atTop (𝓝 (Real.exp (-scale / 4))) := by
  simpa only [pGuess_productRecord, PureRecordDecodingThreshold.singleSuccess] using
    PureRecordDecodingThreshold.joint_success_crossover _ copies scale hzero hne hscale

/-- Joint POVMs on the original carriers attain the exact optimum at each index.
Their success converges to the finite-scale limit, and every competing success is
eventually within any positive tolerance above that limit, uniformly over the POVMs. -/
theorem productRecordPOVM_crossover
    (A : ℕ → Type*) [∀ n, Fintype (A n)] [∀ n, DecidableEq (A n)]
    (v : ∀ n, Bool → A n → ℂ)
    (hv : ∀ n b, star (v n b) ⬝ᵥ v n b = 1) (copies : ℕ → ℕ) (scale : ℝ)
    (hzero : Tendsto (fun n => ‖star (v n false) ⬝ᵥ v n true‖ ^ 2) atTop (𝓝 0))
    (hne : ∀ᶠ n in atTop, ‖star (v n false) ⬝ᵥ v n true‖ ^ 2 ≠ 0)
    (hscale : Tendsto (fun n => (copies n : ℝ) * ‖star (v n false) ⬝ᵥ v n true‖ ^ 2)
      atTop (𝓝 scale)) :
    (∃ M : (n : ℕ) → Word (copies n) →
        Matrix (Fin (copies n) → A n) (Fin (copies n) → A n) ℂ,
      (∀ n, (∀ j, (M n j).PosSemidef) ∧ (∑ j, M n j) = 1 ∧
        successProbability (uniformPrior (Word (copies n))) (productRecordState (v n) (hv n))
          (M n) = pGuess (uniformPrior (Word (copies n))) (productRecordState (v n) (hv n))) ∧
      Tendsto (fun n => successProbability (uniformPrior (Word (copies n)))
        (productRecordState (v n) (hv n)) (M n)) atTop (𝓝 (Real.exp (-scale / 4)))) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ a ∈ successProbabilitySet (uniformPrior (Word (copies n)))
      (productRecordState (v n) (hv n)), a < Real.exp (-scale / 4) + ε := by
  classical
  have hgreatest (n : ℕ) := isGreatest_pGuess_productRecord (v n) (hv n) (copies n)
  have hattains (n : ℕ) : ∃ M : Word (copies n) →
      Matrix (Fin (copies n) → A n) (Fin (copies n) → A n) ℂ,
      (∀ j, (M j).PosSemidef) ∧ (∑ j, M j) = 1 ∧
      pGuess (uniformPrior (Word (copies n))) (productRecordState (v n) (hv n)) =
        successProbability (uniformPrior (Word (copies n))) (productRecordState (v n) (hv n)) M :=
    (hgreatest n).1
  choose M hpos hsum hvalue using hattains
  have hlimit := pGuess_productRecord_crossover A v hv copies scale hzero hne hscale
  refine ⟨⟨M, fun n => ⟨hpos n, hsum n, (hvalue n).symm⟩, hlimit.congr hvalue⟩, ?_⟩
  intro ε hε
  filter_upwards [hlimit.eventually_lt_const (lt_add_of_pos_right _ hε)] with n hn
  intro a ha
  exact ((hgreatest n).2 ha).trans_lt hn

end

end JointRecordDecoding
