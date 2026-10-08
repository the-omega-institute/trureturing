/- GID: D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.claim; result=D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.result; claim=D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.claim
   digest: The Birman weight expansion conjecture fails at order two and p = 11/10. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#14466; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.

Consumed private declarations (proof_shape: bind-only):
  nonnegative_series_slopes -> no_nonnegative_expansion.
  rpow_mul_predecessor_strictConvex -> grad_two_gT_pos.
  gT_two -> grad_two_gT_pos, g_98_bounds, g_99_bounds, g_100_bounds, g_101_bounds, g_102_bounds,
    g_198_bounds, g_199_bounds, g_200_bounds, g_201_bounds, g_202_bounds, g_398_bounds,
    g_399_bounds, g_400_bounds, g_401_bounds, g_402_bounds.
  grad_two -> grad_two_gT_pos, B_100_bounds, B_101_bounds, B_102_bounds, B_200_bounds,
    B_201_bounds, B_202_bounds, B_400_bounds, B_401_bounds, B_402_bounds.
  dv_two -> G_formula.
  spow_of_pos -> G_formula.
  grad_two_gT_pos -> G_formula, B_100_root_bounds, B_101_root_bounds, B_102_root_bounds,
    B_200_root_bounds, B_201_root_bounds, B_202_root_bounds, B_400_root_bounds, B_401_root_bounds,
    B_402_root_bounds.
  root_bounds -> g_98_bounds, g_99_bounds, g_100_bounds, g_101_bounds, g_102_bounds,
    B_100_root_bounds, B_101_root_bounds, B_102_root_bounds, denominator_100_bounds,
    scaling_100_bounds, g_198_bounds, g_199_bounds, g_200_bounds, g_201_bounds, g_202_bounds,
    B_200_root_bounds, B_201_root_bounds, B_202_root_bounds, denominator_200_bounds,
    scaling_200_bounds, g_398_bounds, g_399_bounds, g_400_bounds, g_401_bounds, g_402_bounds,
    B_400_root_bounds, B_401_root_bounds, B_402_root_bounds, denominator_400_bounds,
    scaling_400_bounds.
  G_formula -> G_100_bounds, G_200_bounds, G_400_bounds.
  g_98_bounds -> B_100_bounds.
  g_99_bounds -> B_100_bounds, B_101_bounds.
  g_100_bounds -> B_100_bounds, B_101_bounds, B_102_bounds, denominator_100_bounds.
  g_101_bounds -> B_101_bounds, B_102_bounds.
  g_102_bounds -> B_102_bounds.
  B_100_bounds -> B_100_root_bounds.
  B_100_root_bounds -> G_100_bounds.
  B_101_bounds -> B_101_root_bounds.
  B_101_root_bounds -> G_100_bounds.
  B_102_bounds -> B_102_root_bounds.
  B_102_root_bounds -> G_100_bounds.
  denominator_100_bounds -> G_100_bounds.
  scaling_100_bounds -> G_100_bounds.
  G_100_bounds -> certified_slope_gap_bounds.
  g_198_bounds -> B_200_bounds.
  g_199_bounds -> B_200_bounds, B_201_bounds.
  g_200_bounds -> B_200_bounds, B_201_bounds, B_202_bounds, denominator_200_bounds.
  g_201_bounds -> B_201_bounds, B_202_bounds.
  g_202_bounds -> B_202_bounds.
  B_200_bounds -> B_200_root_bounds.
  B_200_root_bounds -> G_200_bounds.
  B_201_bounds -> B_201_root_bounds.
  B_201_root_bounds -> G_200_bounds.
  B_202_bounds -> B_202_root_bounds.
  B_202_root_bounds -> G_200_bounds.
  denominator_200_bounds -> G_200_bounds.
  scaling_200_bounds -> G_200_bounds.
  G_200_bounds -> certified_slope_gap_bounds.
  g_398_bounds -> B_400_bounds.
  g_399_bounds -> B_400_bounds, B_401_bounds.
  g_400_bounds -> B_400_bounds, B_401_bounds, B_402_bounds, denominator_400_bounds.
  g_401_bounds -> B_401_bounds, B_402_bounds.
  g_402_bounds -> B_402_bounds.
  B_400_bounds -> B_400_root_bounds.
  B_400_root_bounds -> G_400_bounds.
  B_401_bounds -> B_401_root_bounds.
  B_401_root_bounds -> G_400_bounds.
  B_402_bounds -> B_402_root_bounds.
  B_402_root_bounds -> G_400_bounds.
  denominator_400_bounds -> G_400_bounds.
  scaling_400_bounds -> G_400_bounds.
  G_400_bounds -> certified_slope_gap_bounds.
  certified_slope_gap_bounds -> certified_slope_failure.
  certified_slope_failure -> no_nonnegative_expansion.
  no_nonnegative_expansion -> result.
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Mul
import Mathlib.Algebra.Group.ForwardDiff

noncomputable section
namespace D5.S3.Analytic.SeriesInequalities.StampachWaclawekExpansionRefutation

/-- The continuous interpolation of the second-order Birman sequence is strictly convex. -/
private theorem rpow_mul_predecessor_strictConvex {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ a * (x - 1)) := by
  have h := (strictConvexOn_rpow (p := a + 1) (by linarith)).sub_concaveOn
    (Real.concaveOn_rpow ha.le ha1.le)
  apply h.congr
  intro x hx
  change 0 ≤ x at hx
  change x ^ (a + 1) - x ^ a = x ^ a * (x - 1)
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [Real.zero_rpow (ne_of_gt ha), Real.zero_rpow (by linarith : a + 1 ≠ 0)]
  · rw [Real.rpow_add hx, Real.rpow_one]
    ring

/-- Nonnegative power-series coefficients force the adjacent secant slopes to increase.
Only convergence at the three points is needed. -/
private theorem nonnegative_series_slopes {c : ℕ → ℝ} {x₁ x₂ x₃ G₁ G₂ G₃ : ℝ}
    (hc : ∀ k, 0 ≤ c k) (hx₃ : 0 ≤ x₃) (h₃₂ : x₃ < x₂) (h₂₁ : x₂ < x₁)
    (h₁ : HasSum (fun k => c k * x₁ ^ k) G₁)
    (h₂ : HasSum (fun k => c k * x₂ ^ k) G₂)
    (h₃ : HasSum (fun k => c k * x₃ ^ k) G₃) :
    (G₂ - G₃) / (x₂ - x₃) ≤ (G₁ - G₂) / (x₁ - x₂) := by
  apply hasSum_le _ ((h₂.sub h₃).div_const (x₂ - x₃))
    ((h₁.sub h₂).div_const (x₁ - x₂))
  intro k
  have hpow := (convexOn_pow (𝕜 := ℝ) k).slope_mono_adjacent hx₃
    (hx₃.trans (h₃₂.trans h₂₁).le) h₃₂ h₂₁
  have h := mul_le_mul_of_nonneg_left hpow (hc k)
  convert h using 1 <;> ring


def gT (ℓ : ℕ) (p : ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then (n : ℝ) ^ (1 - 1 / p) *
    ∏ j ∈ Finset.Icc 1 (ℓ - 1), ((n : ℝ) - j) else 0

def grad (u : ℤ → ℝ) (n : ℤ) : ℝ := u n - u (n - 1)
def dv (u : ℤ → ℝ) (n : ℤ) : ℝ := fwdDiff (1 : ℤ) u n

def spow (a ν : ℝ) : ℝ := if ν = 0 then 0 else ν * |ν| ^ (a - 1)

def rhoT (ℓ : ℕ) (p : ℝ) (n : ℤ) : ℝ :=
  ((-1 : ℝ) ^ ℓ * (dv^[ℓ] (fun m => spow (p - 1)
    ((grad^[ℓ] (gT ℓ p)) m))) n) / (gT ℓ p n) ^ (p - 1)

def claim : Prop := ∀ ℓ : ℕ, ℓ ≥ 1 → ∀ p : ℝ, p > 1 →
  ∃ c : ℕ → ℝ, (∀ k, 0 ≤ c k) ∧ ∀ n : ℕ, ℓ ≤ n →
    HasSum (fun k => c k / (n : ℝ) ^ k) ((n : ℝ) ^ ((ℓ : ℝ) * p) * rhoT ℓ p n)

private theorem gT_two {p : ℝ} {n : ℤ} (hn : 0 ≤ n) :
    gT 2 p n = (n : ℝ) ^ (1 - 1 / p) * ((n : ℝ) - 1) := by
  simp [gT, hn, Finset.Icc_self]

private theorem grad_two (u : ℤ → ℝ) (n : ℤ) :
    (grad^[2] u) n = u n - 2 * u (n - 1) + u (n - 2) := by
  have h := fwdDiff_iter_eq_sum_shift (-1 : ℤ) u 2 n
  norm_num [Finset.sum_range_succ, smul_eq_mul] at h
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, grad]
  simp only [fwdDiff] at h
  have hn : n - 1 - 1 = n - 2 := by omega
  simp only [← sub_eq_add_neg, hn] at h ⊢
  linarith only [h]

private theorem dv_two (u : ℤ → ℝ) (n : ℤ) :
    (dv^[2] u) n = u (n + 2) - 2 * u (n + 1) + u n := by
  change (fwdDiff (1 : ℤ))^[2] u n = _
  rw [fwdDiff_iter_eq_sum_shift]
  norm_num [Finset.sum_range_succ, smul_eq_mul]
  ring

private theorem spow_of_pos {a ν : ℝ} (hν : 0 < ν) : spow a ν = ν ^ a := by
  rw [spow, if_neg (ne_of_gt hν), abs_of_pos hν]
  nth_rw 1 [← Real.rpow_one ν]
  rw [← Real.rpow_add hν]
  congr 1
  ring

/-- General positivity, including the endpoint n = 2 where the zero extension is used. -/
private theorem grad_two_gT_pos {p : ℝ} (hp : 1 < p) {n : ℤ} (hn : 2 ≤ n) :
    0 < (grad^[2] (gT 2 p)) n := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have ha : 0 < 1 - 1 / p := sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have ha1 : 1 - 1 / p < 1 := by have := one_div_pos.mpr hp0; linarith
  have hcv := rpow_mul_predecessor_strictConvex ha ha1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) - 2 := by exact_mod_cast (show 0 ≤ n - 2 by omega)
  have h := hcv.slope_strict_mono_adjacent (x := (n : ℝ) - 2)
    (y := (n : ℝ) - 1) (z := (n : ℝ)) hn0 (by change 0 ≤ (n : ℝ); linarith)
    (by linarith) (by linarith)
  norm_num at h
  rw [grad_two, gT_two (by omega), gT_two (by omega), gT_two (by omega)]
  push_cast
  simp only [one_div] at *
  linarith

private theorem root_bounds {x lo hi : ℝ} {m : ℕ} (hm : m ≠ 0)
    (hx : 0 ≤ x) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hl : lo ^ m ≤ x) (hu : x ≤ hi ^ m) :
    lo ≤ x ^ (1 / (m : ℝ)) ∧ x ^ (1 / (m : ℝ)) ≤ hi := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  simp only [one_div]
  constructor
  · exact (Real.le_rpow_inv_iff_of_pos hlo hx hmR).2
      (by simpa only [one_div, Real.rpow_natCast] using hl)
  · exact (Real.rpow_inv_le_iff_of_pos hx hhi hmR).2
      (by simpa only [one_div, Real.rpow_natCast] using hu)


private def G (n : ℕ) : ℝ := (n : ℝ) ^ (2 * (11 / 10 : ℝ)) * rhoT 2 (11 / 10) n

private def B (n : ℤ) : ℝ := (grad^[2] (gT 2 (11 / 10))) n

private theorem G_formula {n : ℕ} (hn : 2 ≤ n) :
    G n = (n : ℝ) ^ (2 * (11 / 10 : ℝ)) *
      ((B n) ^ (1 / 10 : ℝ) - 2 * (B (n + 1)) ^ (1 / 10 : ℝ) +
        (B (n + 2)) ^ (1 / 10 : ℝ)) / (gT 2 (11 / 10) n) ^ (1 / 10 : ℝ) := by
  have hp : (1 : ℝ) < 11 / 10 := by norm_num
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have h₀ := grad_two_gT_pos hp hn'
  have h₁ := grad_two_gT_pos hp (show (2 : ℤ) ≤ (n : ℤ) + 1 by omega)
  have h₂ := grad_two_gT_pos hp (show (2 : ℤ) ≤ (n : ℤ) + 2 by omega)
  unfold G rhoT
  rw [dv_two]
  norm_num only [show (11 / 10 : ℝ) - 1 = 1 / 10 by norm_num, neg_one_sq, one_mul]
  rw [spow_of_pos h₀, spow_of_pos h₁, spow_of_pos h₂]
  unfold B
  ring

private theorem g_98_bounds : (1471608496455019764384297529 / 10000000000000000000000000 : ℝ) ≤ gT
  2 (11 / 10) 98 ∧ gT 2 (11 / 10) 98 ≤ (735804248227509882192148813 / 5000000000000000000000000 :
  ℝ) := by
  have h := root_bounds (m := 11) (x := (98 : ℝ)) (lo := (15171221612938348086436057 /
    10000000000000000000000000 : ℝ)) (hi := (7585610806469174043218029 / 5000000000000000000000000
    : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_99_bounds : (744076282112756344850078519 / 5000000000000000000000000 : ℝ) ≤ gT 2
  (11 / 10) 99 ∧ gT 2 (11 / 10) 99 ≤ (93009535264094543106259821 / 625000000000000000000000 : ℝ)
  := by
  have h := root_bounds (m := 11) (x := (99 : ℝ)) (lo := (15185230247199109078573031 /
    10000000000000000000000000 : ℝ)) (hi := (1898153780899888634821629 / 1250000000000000000000000
    : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_100_bounds : (752355986061702189966496731 / 5000000000000000000000000 : ℝ) ≤ gT
  2 (11 / 10) 100 ∧ gT 2 (11 / 10) 100 ≤ (1504711972123404379932993561 /
  10000000000000000000000000 : ℝ) := by
  have h := root_bounds (m := 11) (x := (100 : ℝ)) (lo := (7599555414764668585520169 /
    5000000000000000000000000 : ℝ)) (hi := (15199110829529337171040339 /
    10000000000000000000000000 : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_101_bounds : (7606432896779764236844801 / 50000000000000000000000 : ℝ) ≤ gT 2
  (11 / 10) 101 ∧ gT 2 (11 / 10) 101 ≤ (15212865793559528473689603 / 100000000000000000000000 : ℝ)
  := by
  have h := root_bounds (m := 11) (x := (101 : ℝ)) (lo := (7606432896779764236844801 /
    5000000000000000000000000 : ℝ)) (hi := (15212865793559528473689603 /
    10000000000000000000000000 : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_102_bounds : (38446906195418942474222203 / 250000000000000000000000 : ℝ) ≤ gT 2
  (11 / 10) 102 ∧ gT 2 (11 / 10) 102 ≤ (1537876247816757698968888221 / 10000000000000000000000000
  : ℝ) := by
  have h := root_bounds (m := 11) (x := (102 : ℝ)) (lo := (380662437578405371031903 /
    250000000000000000000000 : ℝ)) (hi := (15226497503136214841276121 / 10000000000000000000000000
    : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem B_100_bounds : (15340127398764916976719 / 10000000000000000000000000 : ℝ) ≤ B 100
  ∧ B 100 ≤ (15340127398764916977111 / 10000000000000000000000000 : ℝ) := by
  have h₀ := g_100_bounds
  have h₁ := g_99_bounds
  have h₂ := g_98_bounds
  norm_num only [B, grad_two, Int.reduceSub]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem B_100_root_bounds : (1307744509421632754544653 / 2500000000000000000000000 : ℝ) ≤
  (B 100) ^ (1 / 10 : ℝ) ∧ (B 100) ^ (1 / 10 : ℝ) ≤ (261548901884326550909599 /
  500000000000000000000000 : ℝ) := by
  have h := B_100_bounds
  apply root_bounds (m := 10) (by decide)
    (le_of_lt (grad_two_gT_pos (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (1307744509421632754544653 / 2500000000000000000000000 : ℝ) ^
    (10 : ℕ) ≤ (15340127398764916976719 / 10000000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (15340127398764916977111 / 10000000000000000000000000 : ℝ) ≤
    (261548901884326550909599 / 500000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem B_101_bounds : (3799833664194300782529 / 2500000000000000000000000 : ℝ) ≤ B 101 ∧
  B 101 ≤ (949958416048575195657 / 625000000000000000000000 : ℝ) := by
  have h₀ := g_101_bounds
  have h₁ := g_100_bounds
  have h₂ := g_99_bounds
  norm_num only [B, grad_two, Int.reduceSub]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem B_101_root_bounds : (1306539266310089767815877 / 2500000000000000000000000 : ℝ) ≤
  (B 101) ^ (1 / 10 : ℝ) ∧ (B 101) ^ (1 / 10 : ℝ) ≤ (41809256521922872570217 /
  80000000000000000000000 : ℝ) := by
  have h := B_101_bounds
  apply root_bounds (m := 10) (by decide)
    (le_of_lt (grad_two_gT_pos (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (1306539266310089767815877 / 2500000000000000000000000 : ℝ) ^
    (10 : ℕ) ≤ (3799833664194300782529 / 2500000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (949958416048575195657 / 625000000000000000000000 : ℝ) ≤
    (41809256521922872570217 / 80000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem B_102_bounds : (7530614128192081980491 / 5000000000000000000000000 : ℝ) ≤ B 102 ∧
  B 102 ≤ (7530614128192081980691 / 5000000000000000000000000 : ℝ) := by
  have h₀ := g_102_bounds
  have h₁ := g_101_bounds
  have h₂ := g_100_bounds
  norm_num only [B, grad_two, Int.reduceSub]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem B_102_root_bounds : (652673608684162292843153 / 1250000000000000000000000 : ℝ) ≤
  (B 102) ^ (1 / 10 : ℝ) ∧ (B 102) ^ (1 / 10 : ℝ) ≤ (1305347217368324585689773 /
  2500000000000000000000000 : ℝ) := by
  have h := B_102_bounds
  apply root_bounds (m := 10) (by decide)
    (le_of_lt (grad_two_gT_pos (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (652673608684162292843153 / 1250000000000000000000000 : ℝ) ^ (10
    : ℕ) ≤ (7530614128192081980491 / 5000000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (7530614128192081980691 / 5000000000000000000000000 : ℝ) ≤
    (1305347217368324585689773 / 2500000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem denominator_100_bounds :
    (3301986803862224802677497 / 2000000000000000000000000 : ℝ) ≤ (gT 2 (11 / 10) 100) ^ (1 / 10 :
      ℝ) ∧ (gT 2 (11 / 10) 100) ^ (1 / 10 : ℝ) ≤ (16509934019311124013387487 /
      10000000000000000000000000 : ℝ) := by
  have h := g_100_bounds
  apply root_bounds (m := 10) (by decide) (le_trans (by norm_num) h.1)
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (3301986803862224802677497 / 2000000000000000000000000 : ℝ) ^
    (10 : ℕ) ≤ (752355986061702189966496731 / 5000000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (1504711972123404379932993561 / 10000000000000000000000000 :
    ℝ) ≤ (16509934019311124013387487 / 10000000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem scaling_100_bounds : (251188643150958011108503206779 / 10000000000000000000000000
  : ℝ) ≤ (100 : ℝ) ^ (2 * (11 / 10 : ℝ)) ∧ (100 : ℝ) ^ (2 * (11 / 10 : ℝ)) ≤
  (12559432157547900555425160339 / 500000000000000000000000 : ℝ) := by
  have he : (100 : ℝ) ^ (2 * (11 / 10 : ℝ)) = ((100 : ℝ) ^ (11 : ℕ)) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)]
    norm_num
  rw [he]
  apply root_bounds (m := 5) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem G_100_bounds : (80296519661 / 1000000000000 : ℝ) ≤ G 100 ∧ G 100 ≤ (40148259831 /
  500000000000 : ℝ) := by
  have hs := scaling_100_bounds
  have hd := denominator_100_bounds
  have h₀ := B_100_root_bounds
  have h₁ := B_101_root_bounds
  have h₂ := B_102_root_bounds
  let N : ℝ := (B 100) ^ (1 / 10 : ℝ) - 2 * (B 101) ^ (1 / 10 : ℝ) + (B 102) ^ (1 / 10 : ℝ)
  have hN : (26388339555609184793 / 5000000000000000000000000 : ℝ) ≤ N ∧ N ≤ (6597084888902303007
    / 1250000000000000000000000 : ℝ) := by
    dsimp [N]
    constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]
  have hNpos : 0 ≤ N := le_trans (by norm_num) hN.1
  have hdpos : 0 < (gT 2 (11 / 10) 100) ^ (1 / 10 : ℝ) := lt_of_lt_of_le (by norm_num) hd.1
  rw [G_formula (by norm_num)]
  change (80296519661 / 1000000000000 : ℝ) ≤ (100 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N / (gT 2 (11 / 10)
    100) ^ (1 / 10 : ℝ) ∧ (100 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N / (gT 2 (11 / 10) 100) ^ (1 / 10 :
    ℝ) ≤ (40148259831 / 500000000000 : ℝ)
  constructor
  · apply (le_div_iff₀ hdpos).2
    calc
      (80296519661 / 1000000000000 : ℝ) * (gT 2 (11 / 10) 100) ^ (1 / 10 : ℝ) ≤ (80296519661 /
        1000000000000 : ℝ) * (16509934019311124013387487 / 10000000000000000000000000 : ℝ) :=
        mul_le_mul_of_nonneg_left hd.2 (by norm_num)
      _ ≤ (251188643150958011108503206779 / 10000000000000000000000000 : ℝ) *
        (26388339555609184793 / 5000000000000000000000000 : ℝ) := by norm_num
      _ ≤ (100 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N :=
        mul_le_mul hs.1 hN.1 (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  · apply (div_le_iff₀ hdpos).2
    calc
      (100 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N ≤ (12559432157547900555425160339 /
        500000000000000000000000 : ℝ) * (6597084888902303007 / 1250000000000000000000000 : ℝ) :=
        mul_le_mul hs.2 hN.2 hNpos (by norm_num)
      _ ≤ (40148259831 / 500000000000 : ℝ) * (3301986803862224802677497 /
        2000000000000000000000000 : ℝ) := by norm_num
      _ ≤ (40148259831 / 500000000000 : ℝ) * (gT 2 (11 / 10) 100) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hd.1 (by norm_num)

private theorem g_198_bounds : (1593030075338550870785114617 / 5000000000000000000000000 : ℝ) ≤ gT
  2 (11 / 10) 198 ∧ gT 2 (11 / 10) 198 ≤ (3186060150677101741570229431 /
  10000000000000000000000000 : ℝ) := by
  have h := root_bounds (m := 11) (x := (198 : ℝ)) (lo := (8086447082936806450685861 /
    5000000000000000000000000 : ℝ)) (hi := (16172894165873612901371723 /
    10000000000000000000000000 : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_199_bounds : (1601849971748780686401636717 / 5000000000000000000000000 : ℝ) ≤ gT
  2 (11 / 10) 199 ∧ gT 2 (11 / 10) 199 ≤ (100115623234298792900102301 / 312500000000000000000000 :
  ℝ) := by
  have h := root_bounds (m := 11) (x := (199 : ℝ)) (lo := (16180302744937178650521583 /
    10000000000000000000000000 : ℝ)) (hi := (1011268921558573665657599 / 625000000000000000000000
    : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_200_bounds : (805336958430932841207225313 / 2500000000000000000000000 : ℝ) ≤ gT
  2 (11 / 10) 200 ∧ gT 2 (11 / 10) 200 ≤ (3221347833723731364828901451 /
  10000000000000000000000000 : ℝ) := by
  have h := root_bounds (m := 11) (x := (200 : ℝ)) (lo := (4046919389100165031192087 /
    2500000000000000000000000 : ℝ)) (hi := (16187677556400660124768349 /
    10000000000000000000000000 : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_201_bounds : (16195018921862375403363801 / 50000000000000000000000 : ℝ) ≤ gT 2
  (11 / 10) 201 ∧ gT 2 (11 / 10) 201 ≤ (8097509460931187701681901 / 25000000000000000000000 : ℝ)
  := by
  have h := root_bounds (m := 11) (x := (201 : ℝ)) (lo := (16195018921862375403363801 /
    10000000000000000000000000 : ℝ)) (hi := (8097509460931187701681901 / 5000000000000000000000000
    : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_202_bounds : (1628333879406796548228055293 / 5000000000000000000000000 : ℝ) ≤ gT
  2 (11 / 10) 202 ∧ gT 2 (11 / 10) 202 ≤ (3256667758813593096456110787 /
  10000000000000000000000000 : ℝ) := by
  have h := root_bounds (m := 11) (x := (202 : ℝ)) (lo := (8101163579138291284716693 /
    5000000000000000000000000 : ℝ)) (hi := (16202327158276582569433387 /
    10000000000000000000000000 : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem B_200_bounds : (4048702855180396291611 / 5000000000000000000000000 : ℝ) ≤ B 200 ∧
  B 200 ≤ (4048702855180396292007 / 5000000000000000000000000 : ℝ) := by
  have h₀ := g_200_bounds
  have h₁ := g_199_bounds
  have h₂ := g_198_bounds
  norm_num only [B, grad_two, Int.reduceSub]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem B_200_root_bounds : (4907209393317845174220493 / 10000000000000000000000000 : ℝ) ≤
  (B 200) ^ (1 / 10 : ℝ) ∧ (B 200) ^ (1 / 10 : ℝ) ≤ (4907209393317845174268491 /
  10000000000000000000000000 : ℝ) := by
  have h := B_200_bounds
  apply root_bounds (m := 10) (by decide)
    (le_of_lt (grad_two_gT_pos (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (4907209393317845174220493 / 10000000000000000000000000 : ℝ) ^
    (10 : ℕ) ≤ (4048702855180396291611 / 5000000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (4048702855180396292007 / 5000000000000000000000000 : ℝ) ≤
    (4907209393317845174268491 / 10000000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem B_201_bounds : (2015105643430954557683 / 2500000000000000000000000 : ℝ) ≤ B 201 ∧
  B 201 ≤ (1007552821715477278941 / 1250000000000000000000000 : ℝ) := by
  have h₀ := g_201_bounds
  have h₁ := g_200_bounds
  have h₂ := g_199_bounds
  norm_num only [B, grad_two, Int.reduceSub]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem B_201_root_bounds : (4904963512545529511458057 / 10000000000000000000000000 : ℝ) ≤
  (B 201) ^ (1 / 10 : ℝ) ∧ (B 201) ^ (1 / 10 : ℝ) ≤ (4904963512545529511506497 /
  10000000000000000000000000 : ℝ) := by
  have h := B_201_bounds
  apply root_bounds (m := 10) (by decide)
    (le_of_lt (grad_two_gT_pos (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (4904963512545529511458057 / 10000000000000000000000000 : ℝ) ^
    (10 : ℕ) ≤ (2015105643430954557683 / 2500000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (1007552821715477278941 / 1250000000000000000000000 : ℝ) ≤
    (4904963512545529511506497 / 10000000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem B_202_bounds : (4011896187149969745519 / 5000000000000000000000000 : ℝ) ≤ B 202 ∧
  B 202 ≤ (4011896187149969745919 / 5000000000000000000000000 : ℝ) := by
  have h₀ := g_202_bounds
  have h₁ := g_201_bounds
  have h₂ := g_200_bounds
  norm_num only [B, grad_two, Int.reduceSub]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem B_202_root_bounds : (1225682476029416617944959 / 2500000000000000000000000 : ℝ) ≤
  (B 202) ^ (1 / 10 : ℝ) ∧ (B 202) ^ (1 / 10 : ℝ) ≤ (4902729904117666471828719 /
  10000000000000000000000000 : ℝ) := by
  have h := B_202_bounds
  apply root_bounds (m := 10) (by decide)
    (le_of_lt (grad_two_gT_pos (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (1225682476029416617944959 / 2500000000000000000000000 : ℝ) ^
    (10 : ℕ) ≤ (4011896187149969745519 / 5000000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (4011896187149969745919 / 5000000000000000000000000 : ℝ) ≤
    (4902729904117666471828719 / 10000000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem denominator_200_bounds :
    (3563147147537247471733563 / 2000000000000000000000000 : ℝ) ≤ (gT 2 (11 / 10) 200) ^ (1 / 10 :
      ℝ) ∧ (gT 2 (11 / 10) 200) ^ (1 / 10 : ℝ) ≤ (2226966967210779669833477 /
      1250000000000000000000000 : ℝ) := by
  have h := g_200_bounds
  apply root_bounds (m := 10) (by decide) (le_trans (by norm_num) h.1)
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (3563147147537247471733563 / 2000000000000000000000000 : ℝ) ^
    (10 : ℕ) ≤ (805336958430932841207225313 / 2500000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (3221347833723731364828901451 / 10000000000000000000000000 :
    ℝ) ≤ (2226966967210779669833477 / 1250000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem scaling_200_bounds : (36067497647680338926900580961 / 312500000000000000000000 :
  ℝ) ≤ (200 : ℝ) ^ (2 * (11 / 10 : ℝ)) ∧ (200 : ℝ) ^ (2 * (11 / 10 : ℝ)) ≤
  (1154159924725770845660818590753 / 10000000000000000000000000 : ℝ) := by
  have he : (200 : ℝ) ^ (2 * (11 / 10 : ℝ)) = ((200 : ℝ) ^ (11 : ℕ)) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 200)]
    norm_num
  rw [he]
  apply root_bounds (m := 5) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem G_200_bounds : (39752071871 / 500000000000 : ℝ) ≤ G 200 ∧ G 200 ≤ (79504143743 /
  1000000000000 : ℝ) := by
  have hs := scaling_200_bounds
  have hd := denominator_200_bounds
  have h₀ := B_200_root_bounds
  have h₁ := B_201_root_bounds
  have h₂ := B_202_root_bounds
  let N : ℝ := (B 200) ^ (1 / 10 : ℝ) - 2 * (B 201) ^ (1 / 10 : ℝ) + (B 202) ^ (1 / 10 : ℝ)
  have hN : (2454468890524597467 / 2000000000000000000000000 : ℝ) ≤ N ∧ N ≤ (1534043056577897637 /
    1250000000000000000000000 : ℝ) := by
    dsimp [N]
    constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]
  have hNpos : 0 ≤ N := le_trans (by norm_num) hN.1
  have hdpos : 0 < (gT 2 (11 / 10) 200) ^ (1 / 10 : ℝ) := lt_of_lt_of_le (by norm_num) hd.1
  rw [G_formula (by norm_num)]
  change (39752071871 / 500000000000 : ℝ) ≤ (200 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N / (gT 2 (11 / 10)
    200) ^ (1 / 10 : ℝ) ∧ (200 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N / (gT 2 (11 / 10) 200) ^ (1 / 10 :
    ℝ) ≤ (79504143743 / 1000000000000 : ℝ)
  constructor
  · apply (le_div_iff₀ hdpos).2
    calc
      (39752071871 / 500000000000 : ℝ) * (gT 2 (11 / 10) 200) ^ (1 / 10 : ℝ) ≤ (39752071871 /
        500000000000 : ℝ) * (2226966967210779669833477 / 1250000000000000000000000 : ℝ) :=
        mul_le_mul_of_nonneg_left hd.2 (by norm_num)
      _ ≤ (36067497647680338926900580961 / 312500000000000000000000 : ℝ) * (2454468890524597467 /
        2000000000000000000000000 : ℝ) := by norm_num
      _ ≤ (200 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N :=
        mul_le_mul hs.1 hN.1 (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  · apply (div_le_iff₀ hdpos).2
    calc
      (200 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N ≤ (1154159924725770845660818590753 /
        10000000000000000000000000 : ℝ) * (1534043056577897637 / 1250000000000000000000000 : ℝ) :=
        mul_le_mul hs.2 hN.2 hNpos (by norm_num)
      _ ≤ (79504143743 / 1000000000000 : ℝ) * (3563147147537247471733563 /
        2000000000000000000000000 : ℝ) := by norm_num
      _ ≤ (79504143743 / 1000000000000 : ℝ) * (gT 2 (11 / 10) 200) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hd.1 (by norm_num)

private theorem g_398_bounds : (1368275368677143118501215471 / 2000000000000000000000000 : ℝ) ≤ gT
  2 (11 / 10) 398 ∧ gT 2 (11 / 10) 398 ≤ (855172105423214449063259719 / 1250000000000000000000000
  : ℝ) := by
  have h := root_bounds (m := 11) (x := (398 : ℝ)) (lo := (3446537452587262263227243 /
    2000000000000000000000000 : ℝ)) (hi := (2154085907867038914517027 / 1250000000000000000000000
    : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_399_bounds : (1715043588063740071389055697 / 2500000000000000000000000 : ℝ) ≤ gT
  2 (11 / 10) 399 ∧ gT 2 (11 / 10) 399 ≤ (3430087176127480142778111593 / 5000000000000000000000000
  : ℝ) := by
  have h := root_bounds (m := 11) (x := (399 : ℝ)) (lo := (8618309487757487795924903 /
    5000000000000000000000000 : ℝ)) (hi := (17236618975514975591849807 /
    10000000000000000000000000 : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_400_bounds : (6878976154328544988449773661 / 10000000000000000000000000 : ℝ) ≤
  gT 2 (11 / 10) 400 ∧ gT 2 (11 / 10) 400 ≤ (343948807716427249422488703 /
  500000000000000000000000 : ℝ) := by
  have h := root_bounds (m := 11) (x := (400 : ℝ)) (lo := (17240541740171791951001939 /
    10000000000000000000000000 : ℝ)) (hi := (862027087008589597550097 / 500000000000000000000000 :
    ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_401_bounds : (4311113899891086774493679 / 6250000000000000000000 : ℝ) ≤ gT 2 (11
  / 10) 401 ∧ gT 2 (11 / 10) 401 ≤ (17244455599564347097974717 / 25000000000000000000000 : ℝ) :=
  by
  have h := root_bounds (m := 11) (x := (401 : ℝ)) (lo := (4311113899891086774493679 /
    2500000000000000000000000 : ℝ)) (hi := (17244455599564347097974717 /
    10000000000000000000000000 : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem g_402_bounds : (6916592599012486756480051691 / 10000000000000000000000000 : ℝ) ≤
  gT 2 (11 / 10) 402 ∧ gT 2 (11 / 10) 402 ≤ (1729148149753121689120013023 /
  2500000000000000000000000 : ℝ) := by
  have h := root_bounds (m := 11) (x := (402 : ℝ)) (lo := (17248360596041114105935291 /
    10000000000000000000000000 : ℝ)) (hi := (4312090149010278526483823 / 2500000000000000000000000
    : ℝ))
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [gT_two (by norm_num)]
  norm_num only [show (1 - 1 / (11 / 10) : ℝ) = 1 / 11 by norm_num]
  constructor <;> nlinarith [h.1, h.2]

private theorem B_400_bounds : (1073301085002460851161 / 2500000000000000000000000 : ℝ) ≤ B 400 ∧
  B 400 ≤ (1073301085002460851559 / 2500000000000000000000000 : ℝ) := by
  have h₀ := g_400_bounds
  have h₁ := g_399_bounds
  have h₂ := g_398_bounds
  norm_num only [B, grad_two, Int.reduceSub]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem B_400_root_bounds : (575689315147317345970397 / 1250000000000000000000000 : ℝ) ≤
  (B 400) ^ (1 / 10 : ℝ) ∧ (B 400) ^ (1 / 10 : ℝ) ≤ (2302757260589269383966979 /
  5000000000000000000000000 : ℝ) := by
  have h := B_400_bounds
  apply root_bounds (m := 10) (by decide)
    (le_of_lt (grad_two_gT_pos (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (575689315147317345970397 / 1250000000000000000000000 : ℝ) ^ (10
    : ℕ) ≤ (1073301085002460851161 / 2500000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (1073301085002460851559 / 2500000000000000000000000 : ℝ) ≤
    (2302757260589269383966979 / 5000000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem B_401_bounds : (1070855902286961640267 / 2500000000000000000000000 : ℝ) ≤ B 401 ∧
  B 401 ≤ (535427951143480820333 / 1250000000000000000000000 : ℝ) := by
  have h₀ := g_401_bounds
  have h₁ := g_400_bounds
  have h₂ := g_399_bounds
  norm_num only [B, grad_two, Int.reduceSub]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem B_401_root_bounds : (1151116055182036325659341 / 2500000000000000000000000 : ℝ) ≤
  (B 401) ^ (1 / 10 : ℝ) ∧ (B 401) ^ (1 / 10 : ℝ) ≤ (4604464220728145302808927 /
  10000000000000000000000000 : ℝ) := by
  have h := B_401_bounds
  apply root_bounds (m := 10) (by decide)
    (le_of_lt (grad_two_gT_pos (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (1151116055182036325659341 / 2500000000000000000000000 : ℝ) ^
    (10 : ℕ) ≤ (1070855902286961640267 / 2500000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (535427951143480820333 / 1250000000000000000000000 : ℝ) ≤
    (4604464220728145302808927 / 10000000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem B_402_bounds : (534211194258318756469 / 1250000000000000000000000 : ℝ) ≤ B 402 ∧ B
  402 ≤ (534211194258318756669 / 1250000000000000000000000 : ℝ) := by
  have h₀ := g_402_bounds
  have h₁ := g_401_bounds
  have h₂ := g_400_bounds
  norm_num only [B, grad_two, Int.reduceSub]
  constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]

private theorem B_402_root_bounds : (575427098419171799034539 / 1250000000000000000000000 : ℝ) ≤
  (B 402) ^ (1 / 10 : ℝ) ∧ (B 402) ^ (1 / 10 : ℝ) ≤ (2301708393676687196224329 /
  5000000000000000000000000 : ℝ) := by
  have h := B_402_bounds
  apply root_bounds (m := 10) (by decide)
    (le_of_lt (grad_two_gT_pos (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (575427098419171799034539 / 1250000000000000000000000 : ℝ) ^ (10
    : ℕ) ≤ (534211194258318756469 / 1250000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (534211194258318756669 / 1250000000000000000000000 : ℝ) ≤
    (2301708393676687196224329 / 5000000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem denominator_400_bounds :
    (9609977807268696843820591 / 5000000000000000000000000 : ℝ) ≤ (gT 2 (11 / 10) 400) ^ (1 / 10 :
      ℝ) ∧ (gT 2 (11 / 10) 400) ^ (1 / 10 : ℝ) ≤ (19219955614537393687641183 /
      10000000000000000000000000 : ℝ) := by
  have h := g_400_bounds
  apply root_bounds (m := 10) (by decide) (le_trans (by norm_num) h.1)
    (by norm_num) (by norm_num)
  · exact le_trans (by norm_num : (9609977807268696843820591 / 5000000000000000000000000 : ℝ) ^
    (10 : ℕ) ≤ (6878976154328544988449773661 / 10000000000000000000000000 : ℝ)) h.1
  · exact le_trans h.2 (by norm_num : (343948807716427249422488703 / 500000000000000000000000 : ℝ)
    ≤ (19219955614537393687641183 / 10000000000000000000000000 : ℝ) ^ (10 : ℕ))

private theorem scaling_400_bounds : (53031264277439788807497282309 / 100000000000000000000000 :
  ℝ) ≤ (400 : ℝ) ^ (2 * (11 / 10 : ℝ)) ∧ (400 : ℝ) ^ (2 * (11 / 10 : ℝ)) ≤
  (5303126427743978880749728230901 / 10000000000000000000000000 : ℝ) := by
  have he : (400 : ℝ) ^ (2 * (11 / 10 : ℝ)) = ((400 : ℝ) ^ (11 : ℕ)) ^ (1 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 400)]
    norm_num
  rw [he]
  apply root_bounds (m := 5) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private theorem G_400_bounds : (79107698317 / 1000000000000 : ℝ) ≤ G 400 ∧ G 400 ≤ (39553849159 /
  500000000000 : ℝ) := by
  have hs := scaling_400_bounds
  have hd := denominator_400_bounds
  have h₀ := B_400_root_bounds
  have h₁ := B_401_root_bounds
  have h₂ := B_402_root_bounds
  let N : ℝ := (B 400) ^ (1 / 10 : ℝ) - 2 * (B 401) ^ (1 / 10 : ℝ) + (B 402) ^ (1 / 10 : ℝ)
  have hN : (1433537811277210817 / 5000000000000000000000000 : ℝ) ≤ N ∧ N ≤ (179192226409694243 /
    625000000000000000000000 : ℝ) := by
    dsimp [N]
    constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2]
  have hNpos : 0 ≤ N := le_trans (by norm_num) hN.1
  have hdpos : 0 < (gT 2 (11 / 10) 400) ^ (1 / 10 : ℝ) := lt_of_lt_of_le (by norm_num) hd.1
  rw [G_formula (by norm_num)]
  change (79107698317 / 1000000000000 : ℝ) ≤ (400 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N / (gT 2 (11 / 10)
    400) ^ (1 / 10 : ℝ) ∧ (400 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N / (gT 2 (11 / 10) 400) ^ (1 / 10 :
    ℝ) ≤ (39553849159 / 500000000000 : ℝ)
  constructor
  · apply (le_div_iff₀ hdpos).2
    calc
      (79107698317 / 1000000000000 : ℝ) * (gT 2 (11 / 10) 400) ^ (1 / 10 : ℝ) ≤ (79107698317 /
        1000000000000 : ℝ) * (19219955614537393687641183 / 10000000000000000000000000 : ℝ) :=
        mul_le_mul_of_nonneg_left hd.2 (by norm_num)
      _ ≤ (53031264277439788807497282309 / 100000000000000000000000 : ℝ) * (1433537811277210817 /
        5000000000000000000000000 : ℝ) := by norm_num
      _ ≤ (400 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N :=
        mul_le_mul hs.1 hN.1 (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  · apply (div_le_iff₀ hdpos).2
    calc
      (400 : ℝ) ^ (2 * (11 / 10 : ℝ)) * N ≤ (5303126427743978880749728230901 /
        10000000000000000000000000 : ℝ) * (179192226409694243 / 625000000000000000000000 : ℝ) :=
        mul_le_mul hs.2 hN.2 hNpos (by norm_num)
      _ ≤ (39553849159 / 500000000000 : ℝ) * (9609977807268696843820591 /
        5000000000000000000000000 : ℝ) := by norm_num
      _ ≤ (39553849159 / 500000000000 : ℝ) * (gT 2 (11 / 10) 400) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hd.1 (by norm_num)

private theorem certified_slope_gap_bounds :
    (-257467 / 2500000000 : ℝ) ≤ 200 * G 100 - 600 * G 200 + 400 * G 400 ∧
      200 * G 100 - 600 * G 200 + 400 * G 400 ≤ (-32183 / 312500000 : ℝ) := by
  constructor <;> linarith [G_100_bounds.1, G_100_bounds.2, G_200_bounds.1,
    G_200_bounds.2, G_400_bounds.1, G_400_bounds.2]

private theorem certified_slope_failure :
    (G 100 - G 200) / ((1 / 100 : ℝ) - 1 / 200) <
      (G 200 - G 400) / ((1 / 200 : ℝ) - 1 / 400) := by
  norm_num
  linarith [certified_slope_gap_bounds.2]

private theorem no_nonnegative_expansion : ¬ ∃ c : ℕ → ℝ, (∀ k, 0 ≤ c k) ∧
    ∀ n : ℕ, 2 ≤ n → HasSum (fun k => c k / (n : ℝ) ^ k) (G n) := by
  rintro ⟨c, hc, hsum⟩
  have h₁ : HasSum (fun k => c k * (1 / 100 : ℝ) ^ k) (G 100) := by
    simpa only [G, Nat.cast_ofNat, one_div, inv_pow, div_eq_mul_inv, one_mul] using hsum 100 (by
      norm_num)
  have h₂ : HasSum (fun k => c k * (1 / 200 : ℝ) ^ k) (G 200) := by
    simpa only [G, Nat.cast_ofNat, one_div, inv_pow, div_eq_mul_inv, one_mul] using hsum 200 (by
      norm_num)
  have h₃ : HasSum (fun k => c k * (1 / 400 : ℝ) ^ k) (G 400) := by
    simpa only [G, Nat.cast_ofNat, one_div, inv_pow, div_eq_mul_inv, one_mul] using hsum 400 (by
      norm_num)
  have H := nonnegative_series_slopes hc (by norm_num : (0 : ℝ) ≤ 1 / 400)
    (by norm_num : (1 / 400 : ℝ) < 1 / 200) (by norm_num : (1 / 200 : ℝ) < 1 / 100) h₁ h₂ h₃
  exact (not_le_of_gt certified_slope_failure) H

theorem result : ¬ claim := by
  intro h
  obtain ⟨c, hc, hsum⟩ := h 2 (by norm_num) (11 / 10) (by norm_num)
  apply no_nonnegative_expansion
  refine ⟨c, hc, ?_⟩
  intro n hn
  simpa only [G, Nat.cast_ofNat] using hsum n hn

end D5.S3.Analytic.SeriesInequalities.StampachWaclawekExpansionRefutation
