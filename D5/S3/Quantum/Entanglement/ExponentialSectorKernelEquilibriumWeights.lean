/- GID: D5/S3/Quantum/Entanglement/ExponentialSectorKernelEquilibriumWeights
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/ExponentialSectorKernelEquilibriumWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Determine all endpoint and interior coordinates of recursive exponential weights for arbitrary real site sequences. -/

import D5.S3.Quantum.Entanglement.ExponentialSectorKernel

namespace D5.S3.Quantum.Entanglement.ExponentialSectorKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The endpoint and interior coordinates of the recursive equilibrium weights. -/
theorem equilibrium_weight_endpoint_interior :
    ∀ n : ℕ, ∀ loss : ℕ → ℝ,
      equilibriumWeight (n + 1) loss 0 = 1 / (1 + edge loss 0) ∧
      equilibriumWeight (n + 1) loss (Fin.last (n + 1)) =
        1 / (1 + edge loss n) ∧
      ∀ i : Fin n,
        equilibriumWeight (n + 1) loss i.castSucc.succ =
          1 / (1 + edge loss i) + 1 / (1 + edge loss (i + 1)) - 1 := by
  intro n loss
  classical
  have hden (i : ℕ) : 1 + edge loss i ≠ 0 := by
    have h : 0 < edge loss i := Real.exp_pos _
    linarith
  have hfirst : ∀ m : ℕ,
      equilibriumWeight (m + 1) loss 0 = 1 / (1 + edge loss 0) := by
    intro m
    induction m with
    | zero =>
      change 1 - edge loss 0 / (1 + edge loss 0) = 1 / (1 + edge loss 0)
      field_simp [hden 0] <;> ring
    | succ m ih =>
      have hz : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      rw [show (0 : Fin (m + 3)) = (0 : Fin (m + 2)).castSucc from rfl]
      rw [equilibriumWeight]
      dsimp only
      rw [Fin.lastCases_castSucc]
      simpa only [hz, if_false, sub_zero] using ih
  have hinterior : ∀ m : ℕ, ∀ i : Fin m,
      equilibriumWeight (m + 1) loss i.castSucc.succ =
        1 / (1 + edge loss i) + 1 / (1 + edge loss (i + 1)) - 1 := by
    intro m
    induction m with
    | zero => intro i; exact Fin.elim0 i
    | succ m ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hx : (Fin.last m).castSucc.succ = (Fin.last (m + 1)).castSucc := by
          apply Fin.ext
          simp
        rw [hx]
        rw [equilibriumWeight]
        dsimp only
        rw [Fin.lastCases_castSucc]
        simp only [if_true, equilibriumWeight, Fin.lastCases_last, Fin.val_last]
        field_simp [hden (m + 1)] <;> ring
      · have hx : j.castSucc.castSucc.succ = j.castSucc.succ.castSucc := by
          apply Fin.ext
          rfl
        rw [hx]
        rw [equilibriumWeight]
        dsimp only
        rw [Fin.lastCases_castSucc]
        have hne : j.castSucc.succ ≠ Fin.last (m + 1) := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at hv
          have := j.isLt
          omega
        simpa only [hne, if_false, sub_zero, Fin.val_castSucc] using ih j
  refine ⟨hfirst n, ?_, hinterior n⟩
  simp [equilibriumWeight]

end D5.S3.Quantum.Entanglement.ExponentialSectorKernel
