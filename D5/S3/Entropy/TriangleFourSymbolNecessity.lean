/- GID: D5/S3/Entropy/TriangleFourSymbolNecessity
   generality: G
   mirror-B: D5/B/S3/Entropy/TriangleFourSymbolNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three nonzero pairwise-orthogonal likelihood directions force four output symbols; binary Latin squares are parity and the original block cell law has independent source-pair marginals. -/

import D5.S3.Entropy.EntropyEquality

/-!
# Triangle four-symbol necessity core

This module records the finite weighted-orthogonality and original-source block calculations
used by the support-at-most-four equality classification.
-/

namespace D5.S3.Entropy.TriangleFourSymbolNecessity
noncomputable def wdot {O : Type*} [Fintype O] (p f g : O → ℝ) : ℝ := ∑ x, p x * (f x * g x)
private theorem wdot_self_pos {O : Type*} [Fintype O] {p v : O → ℝ}
    (hp : ∀ x, 0 < p x) (hv : v ≠ 0) : 0 < wdot p v v := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hterm : 0 < p x * (v x * v x) := mul_pos (hp x) (mul_self_pos.mpr hx)
  have hnonneg : ∀ y, 0 ≤ p y * (v y * v y) := by
    intro y; exact mul_nonneg (hp y).le (mul_self_nonneg _)
  rw [wdot]
  exact lt_of_lt_of_le hterm (Finset.single_le_sum (fun y _ => hnonneg y) (Finset.mem_univ x))
structure TriangleLikelihoodFrame (O : Type*) [Fintype O] where
  p : O → ℝ
  hp : ∀ x, 0 < p x
  hpsum : ∑ x, p x = 1
  v₁ : O → ℝ
  v₂ : O → ℝ
  v₃ : O → ℝ
  hmean₁ : ∑ x, p x * v₁ x = 0
  hmean₂ : ∑ x, p x * v₂ x = 0
  hmean₃ : ∑ x, p x * v₃ x = 0
  horth₁₂ : wdot p v₁ v₂ = 0
  horth₁₃ : wdot p v₁ v₃ = 0
  horth₂₃ : wdot p v₂ v₃ = 0
  hnonzero₁ : v₁ ≠ 0
  hnonzero₂ : v₂ ≠ 0
  hnonzero₃ : v₃ ≠ 0

theorem weighted_likelihood_frame_card_ge_four {O : Type*} [Fintype O] (F : TriangleLikelihoodFrame O) : 4 ≤ Fintype.card O := by
  let one : O → ℝ := fun _ => 1
  let basis : Fin 4 → O → ℝ := fun i => match i with
    | 0 => one | 1 => F.v₁ | 2 => F.v₂ | 3 => F.v₃
  have hli : LinearIndependent ℝ basis := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : g 0 • one + g 1 • F.v₁ + g 2 • F.v₂ + g 3 • F.v₃ = 0 := by
      simpa [basis, Fin.sum_univ_four, one, smul_eq_mul, add_assoc] using hg
    have hcoef (a b c d : ℝ)
        (h : a • one + b • F.v₁ + c • F.v₂ + d • F.v₃ = 0) :
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
      have eq0 : ∑ x, F.p x * (a + b * F.v₁ x + c * F.v₂ x + d * F.v₃ x) = 0 := by
        calc
          _ = ∑ x, F.p x * ((a • one + b • F.v₁ + c • F.v₂ + d • F.v₃) x) := by
            apply Finset.sum_congr rfl
            intro x _
            simp [one, smul_eq_mul]
          _ = 0 := by rw [h]; simp
      have eq1 : ∑ x, F.p x * (a + b * F.v₁ x + c * F.v₂ x + d * F.v₃ x) * F.v₁ x = 0 := by
        calc
          _ = ∑ x, (F.p x * ((a • one + b • F.v₁ + c • F.v₂ + d • F.v₃) x)) * F.v₁ x := by
            apply Finset.sum_congr rfl
            intro x _
            simp [one, smul_eq_mul]
          _ = 0 := by rw [h]; simp
      have eq2 : ∑ x, F.p x * (a + b * F.v₁ x + c * F.v₂ x + d * F.v₃ x) * F.v₂ x = 0 := by
        calc
          _ = ∑ x, (F.p x * ((a • one + b • F.v₁ + c • F.v₂ + d • F.v₃) x)) * F.v₂ x := by
            apply Finset.sum_congr rfl
            intro x _
            simp [one, smul_eq_mul]
          _ = 0 := by rw [h]; simp
      have eq3 : ∑ x, F.p x * (a + b * F.v₁ x + c * F.v₂ x + d * F.v₃ x) * F.v₃ x = 0 := by
        calc
          _ = ∑ x, (F.p x * ((a • one + b • F.v₁ + c • F.v₂ + d • F.v₃) x)) * F.v₃ x := by
            apply Finset.sum_congr rfl
            intro x _
            simp [one, smul_eq_mul]
          _ = 0 := by rw [h]; simp
      have ea : a = 0 := by
        have hh : a * ∑ x, F.p x + b * ∑ x, F.p x * F.v₁ x +
            c * ∑ x, F.p x * F.v₂ x + d * ∑ x, F.p x * F.v₃ x = 0 := by
          calc
            _ = ∑ x, F.p x * (a + b * F.v₁ x + c * F.v₂ x + d * F.v₃ x) := by
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x _
              ring
            _ = 0 := eq0
        rw [F.hpsum, F.hmean₁, F.hmean₂, F.hmean₃] at hh
        linarith
      have eb : b = 0 := by
        have hh : a * wdot F.p one F.v₁ + b * wdot F.p F.v₁ F.v₁ +
            c * wdot F.p F.v₂ F.v₁ + d * wdot F.p F.v₃ F.v₁ = 0 := by
          calc
            _ = ∑ x, F.p x * (a + b * F.v₁ x + c * F.v₂ x + d * F.v₃ x) * F.v₁ x := by
              simp only [wdot]
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x _
              simp [one]
              ring
            _ = 0 := eq1
        have hmean : wdot F.p one F.v₁ = 0 := by simpa [wdot, one] using F.hmean₁
        have h12 : wdot F.p F.v₂ F.v₁ = 0 := by simpa [wdot, mul_comm] using F.horth₁₂
        have h13 : wdot F.p F.v₃ F.v₁ = 0 := by simpa [wdot, mul_comm] using F.horth₁₃
        rw [hmean, h12, h13] at hh
        have hpos := wdot_self_pos F.hp F.hnonzero₁
        exact (mul_eq_zero.mp (by simpa [add_assoc, add_left_comm, add_comm] using hh)).resolve_right (ne_of_gt hpos)
      have ec : c = 0 := by
        have hh : a * wdot F.p one F.v₂ + b * wdot F.p F.v₁ F.v₂ +
            c * wdot F.p F.v₂ F.v₂ + d * wdot F.p F.v₃ F.v₂ = 0 := by
          calc
            _ = ∑ x, F.p x * (a + b * F.v₁ x + c * F.v₂ x + d * F.v₃ x) * F.v₂ x := by
              simp only [wdot]
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x _
              simp [one]
              ring
            _ = 0 := eq2
        have hmean : wdot F.p one F.v₂ = 0 := by simpa [wdot, one] using F.hmean₂
        have h23 : wdot F.p F.v₃ F.v₂ = 0 := by simpa [wdot, mul_comm] using F.horth₂₃
        rw [hmean, F.horth₁₂, h23] at hh
        have hpos := wdot_self_pos F.hp F.hnonzero₂
        exact (mul_eq_zero.mp (by simpa [add_assoc, add_left_comm, add_comm] using hh)).resolve_right (ne_of_gt hpos)
      have ed : d = 0 := by
        have hh : a * wdot F.p one F.v₃ + b * wdot F.p F.v₁ F.v₃ +
            c * wdot F.p F.v₂ F.v₃ + d * wdot F.p F.v₃ F.v₃ = 0 := by
          calc
            _ = ∑ x, F.p x * (a + b * F.v₁ x + c * F.v₂ x + d * F.v₃ x) * F.v₃ x := by
              simp only [wdot]
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x _
              simp [one]
              ring
            _ = 0 := eq3
        have hmean : wdot F.p one F.v₃ = 0 := by simpa [wdot, one] using F.hmean₃
        have h13 : wdot F.p F.v₃ F.v₁ = 0 := by simpa [wdot, mul_comm] using F.horth₁₃
        have h23 : wdot F.p F.v₃ F.v₂ = 0 := by simpa [wdot, mul_comm] using F.horth₂₃
        rw [hmean, F.horth₁₃, F.horth₂₃] at hh
        have hpos := wdot_self_pos F.hp F.hnonzero₃
        exact (mul_eq_zero.mp (by simpa [add_assoc, add_left_comm, add_comm] using hh)).resolve_right (ne_of_gt hpos)
      exact ⟨ea, eb, ec, ed⟩
    have hc := hcoef (g 0) (g 1) (g 2) (g 3) hsum
    fin_cases i <;> simp [hc]
  have hc : Fintype.card (Fin 4) ≤ Module.finrank ℝ (O → ℝ) := hli.fintype_card_le_finrank
  simpa [Module.finrank_pi] using hc
/-- A binary Latin square is parity, up to a global relabelling of its output bit. -/
theorem binary_latin_square_is_xor (g : Bool → Bool → Bool)
    (hrow : ∀ u, Function.Injective (g u))
    (hcol : ∀ v, Function.Injective (fun u => g u v)) :
    ∃ c : Bool, ∀ u v, g u v = c ^^ (u ^^ v) := by
  have hrow0 := Bool.injective_iff.mp (hrow false)
  have hrow1 := Bool.injective_iff.mp (hrow true)
  have hcol0 := Bool.injective_iff.mp (hcol false)
  have hcol1 := Bool.injective_iff.mp (hcol true)
  cases h00 : g false false <;> cases h01 : g false true <;>
    cases h10 : g true false <;> cases h11 : g true true <;>
    simp_all [Bool.xor]

noncomputable def binaryBlockCell {S₁ S₂ S₃ O : Type*} (h : Bool × Bool ≃ O)
    (q₁ : Bool → S₁ → ℝ) (q₂ : Bool → S₂ → ℝ) (q₃ : Bool → S₃ → ℝ)
    (x : O) (s : S₁ × S₂ × S₃) : ℝ := by
  classical
  exact ∑ u : Bool, ∑ v : Bool,
    if x = h (u, v) then (1 / 4 : ℝ) * q₁ u s.1 * q₂ v s.2.1 * q₃ (u ^^ v) s.2.2 else 0

/-- The original-source cell law has independent pair marginals, with no source-cardinality
assumption and no deletion of structural zeros. -/
theorem binary_block_source_pair_marginal {S₁ S₂ S₃ : Type*} [Fintype S₃]
    (q₁ : Bool → S₁ → ℝ) (q₂ : Bool → S₂ → ℝ) (q₃ : Bool → S₃ → ℝ)
    (hq₃ : ∀ b, ∑ s₃, q₃ b s₃ = 1) (s₁ : S₁) (s₂ : S₂) :
    (∑ u : Bool, ∑ v : Bool, ∑ s₃,
      (1 / 4 : ℝ) * q₁ u s₁ * q₂ v s₂ * q₃ (u ^^ v) s₃) =
      ((1 / 2 : ℝ) * (q₁ false s₁ + q₁ true s₁)) *
        ((1 / 2 : ℝ) * (q₂ false s₂ + q₂ true s₂)) := by
  classical
  simp_rw [← Finset.mul_sum]
  simp_rw [hq₃]
  simp only [mul_one]
  norm_num [Fintype.sum_bool]
  ring

end D5.S3.Entropy.TriangleFourSymbolNecessity
