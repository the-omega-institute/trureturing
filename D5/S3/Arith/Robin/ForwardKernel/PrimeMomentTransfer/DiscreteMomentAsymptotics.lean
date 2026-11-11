/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteMomentAsymptotics
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteMomentAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square prime correlations: Normalized discrete cubic and fourth moment errors follow from arithmetic transfer and formal interval bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.WeightedArithmeticTransfer
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FormalIntervalMomentBounds

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-! The normalized stage consumes the arithmetic and formal envelopes. -/

theorem discrete_moment_asymptotic_inputs {q : ℕ} (SS : Finset ℕ → ℝ) (α β : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hMS : MeanSquareHL q SS β) (hcor : IntervalCorrelations SS)
    (M : ℝ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      ∀ H : ℕ, N^α ≤ (H : ℝ) → (H : ℝ) ≤ N^β →
      ∀ B (w : ℝ → ℝ), BVBound w B → ∀ k : ℕ, (k = 2 ∨ k = 3 ∨ k = 4) ∧ k ≤ q →
      ∀ a b : Fin k → ℝ, admissible M a b →
        |discreteRaw N H a b w -
          (∫ x in N..2*N, w (x/N) * Phi SS H (Real.log x) a b)| ≤
          C*B*N^(1/2+ε)*(H:ℝ)^k) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∃ η : ℝ → ℝ,
      (∀ H, 0 ≤ η H) ∧ AntitoneOn η (Ici 2) ∧ Tendsto η atTop (nhds 0) ∧
      ∀ᶠ N : ℝ in atTop, ∀ H s : ℝ, N^α ≤ H → H ≤ N^β →
        Real.log N ≤ s → s ≤ Real.log N + Real.log 2 →
        (∀ a b : Fin 3 → ℝ, admissible M a b →
          |Phi SS H s a b| ≤ C*(η H*(H*Real.log N)^(3/2:ℝ)+H*(Real.log N)^2)) ∧
        (∀ a b : Fin 4 → ℝ, admissible M a b →
          |Phi SS H s a b-H^2*(s-Real.log H)^2*W4 a b| ≤
            C*(η H*H^2*(Real.log N)^2+H^2*Real.log N))) := by
  constructor
  · obtain ⟨C, hC, htransfer⟩ := arithmetic_transfer SS α β hα hαβ hβ hSS hSS1 hMS M hM ε hε
    refine ⟨C, hC, ?_⟩
    filter_upwards [htransfer] with N hN
    intro H hlo hhi B w hw k hk a b hab
    exact hN H hlo hhi B w hw k
      ⟨by rcases hk.1 with rfl | rfl | rfl <;> omega, hk.2⟩ a b hab
  · exact formal_interval_moment_bounds SS α β hα hαβ hβ hSS hSS1 hcor M hM

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
