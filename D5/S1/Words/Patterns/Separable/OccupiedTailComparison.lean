/- GID: D5/S1/Words/Patterns/Separable/OccupiedTailComparison
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedTailComparison
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Positive actual forcing closes the finite core of an eventual occupation subsolution. -/

import D5.S1.Words.Patterns.Separable.OccupiedComparison
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! A single scale balances the compensated gain, the quadratic loss, and actual forcing. -/

namespace D5.S1.Words.Patterns.Separable.OccupiedTailComparison

open OccupiedComparison
open CutFactorization (Avoider)
open MinimumCutKernel (identityAvoider)
open Filter
open scoped Topology

private theorem actual_constants : 0 < h ∧ 0 < ceiling ∧ 0 < rho := by
  have h₁ : 1 < Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have h₂ : Real.sqrt (2 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  refine ⟨?_, ?_, ?_⟩
  · unfold h b; linarith
  · unfold ceiling a b; linarith
  · unfold rho b; exact pow_pos (sub_pos.mpr h₁) 2

private theorem actual_forcing_pos (x : ℤ) : 0 < forcing x := by
  have hr := actual_constants.2.2
  unfold forcing
  split_ifs
  · exact hr
  · apply mul_pos (by positivity)
    unfold shapeWeight
    let : Nonempty (Avoider (x.natAbs - 1 + 1)) := ⟨identityAvoider _⟩
    exact mul_pos (pow_pos hr _) (by exact_mod_cast (Nat.card_pos (α := Avoider (x.natAbs-1+1))))

private theorem actual_weights (n : ℕ) :
    0 ≤ kernelWeight n ∧ 0 ≤ lossWeight n ∧ lossWeight n ≤ (3 / 2 : ℝ)*kernelWeight n := by
  have hρ : 0 ≤ rho := actual_constants.2.2.le
  have hs : 0 ≤ shapeWeight n := by unfold shapeWeight; positivity
  unfold kernelWeight lossWeight
  split_ifs <;> exact ⟨by linarith, by linarith, by linarith⟩

private theorem scaled_squares_finite {f : ℤ → ℝ}
    (hf : Summable (fun x => (f x) ^ 2)) (t : ℝ) (ε : ℝ) (hε : 0 < ε) :
    Set.Finite {x : ℤ | ε ≤ t * f x} := by
  have hs : Summable (fun x => (t * f x) ^ 2) := by
    simpa only [mul_pow] using hf.mul_left (t ^ 2)
  have he : ∀ᶠ x in Filter.cofinite, (t * f x) ^ 2 < ε ^ 2 :=
    hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  have he' : ∀ᶠ x in Filter.cofinite, ¬ ε ≤ t * f x := he.mono fun x hx h =>
    (not_le_of_gt hx) (pow_le_pow_left₀ hε.le h 2)
  exact (Filter.eventually_cofinite.mp he').subset (fun _ hx hn => hn hx)

private theorem jump_term_bounds (k : ℕ → ℝ) (hk : ∀ n, 0 ≤ k n)
    (f : ℤ → ℝ) (H : ℝ) (hf : ∀ x, 0 ≤ f x) (hH : ∀ x, f x ≤ H) (x : ℤ) (n : ℕ) :
    0 ≤ k n * f (x + (n + 1 : ℤ)) + k n * f (x - (n + 1 : ℤ)) ∧
    k n * f (x + (n + 1 : ℤ)) + k n * f (x - (n + 1 : ℤ)) ≤ (2 * H) * k n := by
  constructor
  · exact add_nonneg (mul_nonneg (hk n) (hf _)) (mul_nonneg (hk n) (hf _))
  · linarith only [mul_le_mul_of_nonneg_left (hH (x + (n + 1 : ℤ))) (hk n),
      mul_le_mul_of_nonneg_left (hH (x - (n + 1 : ℤ))) (hk n)]

private theorem jump_summable (k : ℕ → ℝ) (hk : ∀ n, 0 ≤ k n) (hks : Summable k)
    (f : ℤ → ℝ) (H : ℝ) (hf : ∀ x, 0 ≤ f x) (hH : ∀ x, f x ≤ H) (x : ℤ) :
    Summable (fun n : ℕ => k n * f (x + (n + 1 : ℤ)) + k n * f (x - (n + 1 : ℤ))) :=
  Summable.of_nonneg_of_le (fun n => (jump_term_bounds k hk f H hf hH x n).1)
    (fun n => (jump_term_bounds k hk f H hf hH x n).2) (hks.mul_left (2 * H))

private theorem core_forcing_minimum (N : ℕ) :
    ∃ m : ℝ, 0 < m ∧ ∀ x : ℤ, |x| ≤ (N : ℤ) → m ≤ forcing x := by
  classical
  let S := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hs : (0 : ℤ) ∈ S := by simp [S]
  have hne : (S.image forcing).Nonempty := ⟨forcing 0, Finset.mem_image_of_mem _ hs⟩
  let m := (S.image forcing).min' hne
  have hm : m ∈ S.image forcing := Finset.min'_mem _ _
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hm
  refine ⟨m, hz ▸ actual_forcing_pos z, fun x hx => ?_⟩
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr (abs_le.mp hx)))

private theorem exact_loss_bound {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ loss u ∧ loss u ≤ u ^ 2 / h := by
  have hh := actual_constants.1
  have hden : 0 < h + u := by linarith
  exact ⟨div_nonneg (sq_nonneg _) hden.le,
    div_le_div_of_nonneg_left (sq_nonneg _) hh (by linarith)⟩

private theorem nonnegative_scaled_neighbor {u : ℝ} (hu : 0 ≤ u) (hh : u ≤ h / 2) (n : ℕ) :
    0 ≤ neighborTerm n u := by
  obtain ⟨hκ, hℓ, hκℓ⟩ := actual_weights n
  have hh0 := actual_constants.1
  have hsmall : u ^ 2 / h ≤ u / 2 := by
    apply (div_le_iff₀ hh0).2
    nlinarith only [mul_le_mul_of_nonneg_left hh hu]
  have hlo := (exact_loss_bound hu).2.trans hsmall
  have h1 := mul_le_mul_of_nonneg_left hlo hℓ
  have h2 := mul_le_mul_of_nonneg_right hκℓ (show 0 ≤ u / 2 by positivity)
  have h3 := mul_nonneg hκ hu
  unfold neighborTerm
  nlinarith only [h1, h2, h3]

/-- Positive actual forcing on the finite core and an eventual compensated quadratic
gain yield one global strictly positive subsolution scale. -/
theorem actual_lower_from_tail_estimates
    (f : ℤ → ℝ) (F A B : ℝ) (N : ℕ)
    (hF : 0 < F) (hA : 0 < A) (hB : 0 ≤ B)
    (hf : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ F)
    (hvanish : Summable fun x => (f x) ^ 2)
    (hgain : ∀ x : ℤ, (N : ℤ) < |x| →
      A * (f x) ^ 2 ≤ ∑' n : ℕ, kernelWeight n *
        (f (x + (n + 1 : ℤ)) + f (x - (n + 1 : ℤ)) - 2 * f x))
    (hcost : ∀ x : ℤ, (N : ℤ) < |x| →
      (∑' n : ℕ, (lossWeight n * (f (x + (n + 1 : ℤ))) ^ 2 +
        lossWeight n * (f (x - (n + 1 : ℤ))) ^ 2)) ≤ B * (f x) ^ 2) :
    ∃ t : ℝ, 0 < t ∧ ∀ x : ℤ, t * f x ≤ rawOccupation x := by
  obtain ⟨m, hm, hmcore⟩ := core_forcing_minimum N
  obtain ⟨hh, hc, _⟩ := actual_constants
  have hks : Summable kernelWeight := critical_shape_masses.2.2.1
  have hls : Summable lossWeight :=
    Summable.of_nonneg_of_le (fun n => (actual_weights n).2.1)
      (fun n => (actual_weights n).2.2) (hks.mul_left (3 / 2 : ℝ))
  obtain ⟨_, _, htotal, _, _, _, _, _, _, _, _, cmp⟩ := actual_occupation_subsolution_comparison
  let t := min (ceiling / F) (min (h / (2 * F)) (min (h * A / (B + 1)) (m / F)))
  have ht : 0 < t :=
    lt_min (div_pos hc hF) (lt_min (div_pos hh (by positivity))
      (lt_min (div_pos (mul_pos hh hA) (by linarith)) (div_pos hm hF)))
  have htcap : t ≤ ceiling / F := min_le_left _ _
  have htsmall : t ≤ h / (2 * F) := (min_le_right _ _).trans (min_le_left _ _)
  have httail : t ≤ h * A / (B + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htcore : t ≤ m / F :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let v (x : ℤ) := t * f x
  have hv0 (x : ℤ) : 0 ≤ v x := mul_nonneg ht.le (hf x)
  have hvF (x : ℤ) : v x ≤ t * F := mul_le_mul_of_nonneg_left (hbound x) ht.le
  have hvc (x : ℤ) : v x ≤ ceiling := (hvF x).trans ((le_div_iff₀ hF).mp htcap)
  have hvh (x : ℤ) : v x ≤ h / 2 := by
    have hh' := (le_div_iff₀ (show 0 < 2*F by positivity)).mp htsmall
    exact (hvF x).trans (by linarith)
  refine ⟨t, ht, cmp v (fun x => ⟨hv0 x, hvc x⟩) (scaled_squares_finite hvanish t) ?_⟩
  intro x
  by_cases hx : (N : ℤ) < |x|
  · let K (n : ℕ) := kernelWeight n * f (x + (n + 1 : ℤ)) +
        kernelWeight n * f (x - (n + 1 : ℤ))
    let C (n : ℕ) := (2 * f x) * kernelWeight n
    let P (y : ℤ) := (t ^ 2 / h) * (f y) ^ 2
    let U (n : ℕ) := lossWeight n * loss (v (x + (n + 1 : ℤ))) +
      lossWeight n * loss (v (x - (n + 1 : ℤ)))
    let V (n : ℕ) := lossWeight n * P (x + (n + 1 : ℤ)) + lossWeight n * P (x - (n + 1 : ℤ))
    have hK : Summable K := jump_summable kernelWeight (fun n => (actual_weights n).1)
      hks f F hf hbound x
    have hC : Summable C := hks.mul_left _
    have hcomp : (∑' n : ℕ, kernelWeight n *
          (f (x + (n + 1 : ℤ)) + f (x - (n + 1 : ℤ)) - 2 * f x)) = (∑' n, K n) - f x := by
      calc
        _ = ∑' n, (K n - C n) := tsum_congr fun n => by dsimp [K,C]; ring
        _ = _ := by rw [hK.tsum_sub hC]; simp only [C, tsum_mul_left, htotal]; ring
    have hgain' := hgain x hx
    rw [hcomp] at hgain'
    have hsq (y : ℤ) : f y ^ 2 ≤ F ^ 2 :=
      pow_le_pow_left₀ (hf y) (hbound y) _
    have hp0 (y : ℤ) : 0 ≤ P y := by dsimp [P]; positivity
    have hpF (y : ℤ) : P y ≤ (t ^ 2 / h) * F ^ 2 :=
      mul_le_mul_of_nonneg_left (hsq y) (by positivity)
    have hLp (y : ℤ) : loss (v y) ≤ P y := by
      apply (exact_loss_bound (hv0 y)).2.trans_eq
      dsimp [v,P]
      ring
    have hU : Summable U := jump_summable lossWeight (fun n => (actual_weights n).2.1)
      hls (fun y => loss (v y)) _ (fun y => (exact_loss_bound (hv0 y)).1)
      (fun y => (hLp y).trans (hpF y)) x
    have hV : Summable V :=
      jump_summable lossWeight (fun n => (actual_weights n).2.1) hls P _ hp0 hpF x
    have hUV := hU.tsum_le_tsum (fun n => add_le_add
      (mul_le_mul_of_nonneg_left (hLp _) (actual_weights n).2.1)
      (mul_le_mul_of_nonneg_left (hLp _) (actual_weights n).2.1)) hV
    have hV' : (∑' n, V n) = (t ^ 2 / h) *
        (∑' n : ℕ, (lossWeight n * (f (x + (n + 1 : ℤ))) ^ 2 +
          lossWeight n * (f (x - (n + 1 : ℤ))) ^ 2)) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n => by dsimp [V,P]; ring
    rw [hV'] at hUV
    have hloss := hUV.trans (mul_le_mul_of_nonneg_left (hcost x hx) (by positivity))
    have hlin := mul_le_mul_of_nonneg_left hgain' ht.le
    have htB : t*B ≤ h*A := by
      have H := (le_div_iff₀ (show 0 < B+1 by linarith)).mp httail
      linarith only [H, ht.le]
    have hcoef : (t ^ 2 / h)*B ≤ t*A := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hh).2
      nlinarith only [mul_le_mul_of_nonneg_left htB ht.le]
    have hcoef' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (f x))
    have hmap : occupationMap v x = forcing x + (t * (∑' n, K n) - ∑' n, U n) := by
      unfold occupationMap
      congr 1
      rw [← tsum_mul_left, ← (hK.mul_left t).tsum_sub hU]
      exact tsum_congr fun n => by
        simp only [neighborTerm, Nat.cast_add, Nat.cast_one]
        dsimp [K,U,v]
        ring
    rw [hmap]
    change t * f x ≤ _
    nlinarith only [hlin, hloss, hcoef', (actual_forcing_pos x).le]
  · have hfmin := ((le_div_iff₀ hF).mp htcore).trans (hmcore x (le_of_not_gt hx))
    have hsum : 0 ≤ (∑' n : ℕ,
        (neighborTerm n (v (x + (n + 1 : ℕ))) + neighborTerm n (v (x - (n + 1 : ℕ))))) :=
      tsum_nonneg fun n => add_nonneg (nonnegative_scaled_neighbor (hv0 _) (hvh _) n)
        (nonnegative_scaled_neighbor (hv0 _) (hvh _) n)
    exact (hvF x).trans (hfmin.trans (by unfold occupationMap; linarith))

#print axioms actual_lower_from_tail_estimates

end D5.S1.Words.Patterns.Separable.OccupiedTailComparison
