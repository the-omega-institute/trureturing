/- GID: D5/S3/Combinatorics/Graph/RectangularCountEntropy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RectangularCountEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric rectangular subadditivity gives a square entropy limit. -/
import Mathlib.Analysis.Subadditive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Square limits from rectangular subadditivity

One-dimensional Fekete limits in a fixed width, followed by an infimum over
widths, suffice. A straight cut bounds the diagonal by each fixed-width limit;
the leftover strip has vanishing area proportion. No periodic-boundary premise
or assumed diagonal limit occurs.
-/

namespace D5.S3.Combinatorics.Graph.RectangularCountEntropy

open Set Filter
open scoped Topology

noncomputable section

/-- A square entropy limit from actual rectangular inequalities. -/
theorem square_log_limit (f : ℕ → ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hsym : ∀ r c, f r c = f c r)
    (hsub : ∀ c, Subadditive (fun r => f r c))
    (hbound : ∀ r c, 0 ≤ f r c ∧ f r c ≤ (r : ℝ) * c * L) :
    ∃ s : ℝ, 0 ≤ s ∧ Tendsto (fun n : ℕ => f n n / (n : ℝ) ^ 2) atTop (𝓝 s) := by
  have hbdd (c : ℕ) : BddBelow (range fun r : ℕ => f r c / r) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact div_nonneg (hbound r c).1 (Nat.cast_nonneg r)
  let g : ℕ → ℝ := fun c => (hsub c).lim
  have hg (c : ℕ) : Tendsto (fun r : ℕ => f r c / r) atTop (𝓝 (g c)) :=
    (hsub c).tendsto_lim (hbdd c)
  have hg0 (c : ℕ) : 0 ≤ g c :=
    ge_of_tendsto' (hg c) fun r => div_nonneg (hbound r c).1 (Nat.cast_nonneg r)
  let S : Set ℝ := (fun k : ℕ => g k / k) '' Ici 1
  have hne : S.Nonempty := ⟨g 1 / 1, 1, by simp, by norm_num⟩
  have hS : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    exact div_nonneg (hg0 k) (Nat.cast_nonneg k)
  have hs0 : 0 ≤ sInf S := by
    apply le_csInf hne
    rintro _ ⟨k, hk, rfl⟩
    exact div_nonneg (hg0 k) (Nat.cast_nonneg k)
  have hslow (n : ℕ) (hn : 0 < n) : sInf S ≤ f n n / (n : ℝ) ^ 2 := by
    have h1 : sInf S ≤ g n / n := csInf_le hS ⟨n, hn, rfl⟩
    have h2 : g n ≤ f n n / n := (hsub n).lim_le_div (hbdd n) hn.ne'
    calc
      sInf S ≤ g n / n := h1
      _ ≤ (f n n / n) / n := div_le_div_of_nonneg_right h2 (Nat.cast_nonneg n)
      _ = f n n / (n : ℝ) ^ 2 := by rw [div_div, pow_two]
  have hupper (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
      f n n / (n : ℝ) ^ 2 ≤ (f n k / n) / k + (k : ℝ) * L / n := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hq : (n / k : ℕ) * k ≤ n := Nat.div_mul_le_self n k
    have hr : n % k < k := Nat.mod_lt n hk
    have hqr := (hsub n).apply_mul_add_le (n / k) k (n % k)
    rw [Nat.mul_comm (n / k) k, Nat.div_add_mod n k] at hqr
    have hqR : (n / k : ℕ) ≤ (n : ℝ) / k := by
      apply (le_div_iff₀ hkR).mpr
      exact_mod_cast hq
    have hrR : (n % k : ℕ) ≤ (k : ℝ) := by exact_mod_cast hr.le
    have hstrip : f (n % k) n ≤ (k : ℝ) * n * L :=
      (hbound _ _).2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hrR (Nat.cast_nonneg n)) hL)
    have hest : f n n ≤ (n : ℝ) / k * f k n + (k : ℝ) * n * L :=
      hqr.trans (add_le_add (mul_le_mul_of_nonneg_right hqR (hbound k n).1) hstrip)
    calc
      f n n / (n : ℝ) ^ 2 ≤
          ((n : ℝ) / k * f k n + (k : ℝ) * n * L) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hest (sq_nonneg _)
      _ = (f n k / n) / k + (k : ℝ) * L / n := by
        rw [hsym k n]
        field_simp [ne_of_gt hnR, ne_of_gt hkR]
        <;> ring
  refine ⟨sInf S, hs0, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro a ha
    exact (eventually_gt_atTop 0).mono fun n hn => ha.trans_le (hslow n hn)
  · intro b hb
    obtain ⟨_, ⟨k, hk, rfl⟩, hkb⟩ := exists_lt_of_csInf_lt hne hb
    have hkpos : 0 < k := hk
    have hlim : Tendsto (fun n : ℕ => (f n k / n) / k + (k : ℝ) * L / n)
        atTop (𝓝 (g k / k)) := by
      simpa using ((hg k).div_const k).add
        ((tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop) :
          Tendsto (fun n : ℕ => (k : ℝ) * L / n) atTop (𝓝 0))
    filter_upwards [hlim.eventually (gt_mem_nhds hkb), eventually_gt_atTop 0] with n hn hn0
    exact (hupper k n hkpos hn0).trans_lt hn

#print axioms square_log_limit

end
end D5.S3.Combinatorics.Graph.RectangularCountEntropy
