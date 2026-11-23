/- GID: D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Angles
   generality: I
   mirror-B: none(waiver:covered-by-round-quaternion-k4-bounds-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cosine estimates for the angles in four-vertex quaternion reconstruction. -/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic

/-! Analytic estimates for midpoint separation and displaced midpoint cosines. -/

open scoped Real

noncomputable section

namespace RoundQuaternionK4Bounds

private def cosTerm (x : ℝ) (j : ℕ) : ℝ := (-1)^j * x^(2*j) / (Nat.factorial (2*j) : ℝ)

private def cosPartial (n : ℕ) (x : ℝ) : ℝ := ∑ j ∈ Finset.range n, cosTerm x j

private theorem cos_taylor (x : ℝ) (hx : 0 ≤ x) (hxπ : x ≤ π) :
    cosPartial 8 x ≤ Real.cos x ∧ Real.cos x ≤ cosPartial 9 x := by
  let f : ℕ → ℝ := fun j => x ^ (2 * (j + 2)) / (Nat.factorial (2 * (j + 2)) : ℝ)
  let base := cosPartial 2 x
  have hs (k : ℕ) : cosPartial (k + 2) x =
      base + ∑ j ∈ Finset.range k, (-1) ^ j * f j := by
    rw [show k + 2 = 2 + k by omega, cosPartial, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f, cosTerm]
    rw [show 2 + j = j + 2 by omega, pow_add (-1 : ℝ)]
    norm_num
    ring
  have hanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    let k := 2 * (n + 2)
    change x ^ (2 * (n + 1 + 2)) / (Nat.factorial (2 * (n + 1 + 2)) : ℝ) ≤
      x ^ k / (Nat.factorial k : ℝ)
    rw [show 2 * (n + 1 + 2) = k + 2 by dsimp [k]; omega,
      pow_add, show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have hf : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have h₁ : (5 : ℝ) ≤ (k : ℝ) + 1 := by
      exact_mod_cast (show 5 ≤ k + 1 by dsimp [k]; omega)
    have h₂ : (6 : ℝ) ≤ (k : ℝ) + 1 + 1 := by linarith
    have hsq : x ^ 2 ≤ ((k : ℝ) + 1 + 1) * (k + 1) := by
      have hmul := mul_le_mul h₂ h₁ (by norm_num) (by positivity)
      nlinarith [Real.pi_lt_four, sq_nonneg (4 - x)]
    apply (div_le_div_iff₀ (by positivity) hf).mpr
    calc
      _ ≤ x ^ k * (((k : ℝ) + 1 + 1) * (k + 1)) * (Nat.factorial k : ℝ) := by
        gcongr
      _ = _ := by ring
  have hlimit : Filter.Tendsto
      (fun k : ℕ => ∑ j ∈ Finset.range k, (-1) ^ j * f j)
      Filter.atTop (nhds (Real.cos x - base)) := by
    have h := (Real.hasSum_cos x).tendsto_sum_nat.comp
      (Filter.tendsto_atTop_mono (fun n : ℕ => show n ≤ n + 2 by omega) Filter.tendsto_id)
    have hh := h.sub_const base
    convert hh using 1
    ext k
    change _ = cosPartial (k + 2) x - base
    rw [hs]
    ring
  have lo := hanti.alternating_series_le_tendsto hlimit 3
  have hi := hanti.tendsto_le_alternating_series hlimit 3
  rw [show 8 = 6 + 2 by decide, hs 6, show 9 = 7 + 2 by decide, hs 7]
  constructor <;> linarith

private def degrees (x : ℝ) : ℝ := x * π / 180

private theorem cos_degrees (x : ℝ) (hx : 0 ≤ x) (hmax : x ≤ 158) :
    cosPartial 8 (x * 314160 / 18000000) ≤ Real.cos (degrees x) ∧
      Real.cos (degrees x) ≤ cosPartial 9 (x * 314159 / 18000000) := by
  have hp₁ : (3.14159 : ℝ) ≤ π := by linarith [Real.pi_gt_d6]
  have hp₂ := Real.pi_lt_d4.le
  have h₁ : x * 314159 / 18000000 ≤ degrees x := by
    unfold degrees
    nlinarith [mul_le_mul_of_nonneg_left hp₁ hx]
  have h₂ : degrees x ≤ x * 314160 / 18000000 := by
    unfold degrees
    nlinarith [mul_le_mul_of_nonneg_left hp₂ hx]
  have hπ : x * 314160 / 18000000 ≤ π := by
    linarith [Real.pi_gt_d6]
  exact ⟨(cos_taylor _ (by positivity) hπ).1.trans
      (Real.cos_le_cos_of_nonneg_of_le_pi (by unfold degrees; positivity) hπ h₂),
    (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (h₂.trans hπ) h₁).trans
      (cos_taylor _ (by positivity) (h₁.trans (h₂.trans hπ))).2⟩

private theorem tan_half_sq (x : ℝ) (hx : Real.cos (x / 2) ≠ 0) :
    Real.tan (x / 2) ^ 2 = (1 - Real.cos x) / (1 + Real.cos x) := by
  rw [Real.tan_eq_sin_div_cos, div_pow, Real.sin_sq_eq_half_sub]
  have hh := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hh ⊢
  rw [hh]
  field_simp [hx]
  ring

private theorem cos_ratio {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 5 * π / 8) :
    Real.cos (4 * b / 5) / Real.cos (b / 2) ≤
      Real.cos (4 * a / 5) / Real.cos (a / 2) := by
  have hcos (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 5 * π / 8) : 0 < Real.cos (x / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hform (x : ℝ) (hc : 0 < Real.cos (x / 2)) :
      Real.cos (4 * x / 5) / Real.cos (x / 2) =
        Real.cos (3 * x / 10) - Real.tan (x / 2) * Real.sin (3 * x / 10) := by
    rw [show 4 * x / 5 = 3 * x / 10 + x / 2 by ring, Real.cos_add, Real.tan_eq_sin_div_cos]
    field_simp [hc.ne'] <;> ring
  rw [hform _ (hcos _ (ha.trans hab) hb), hform _ (hcos _ ha (hab.trans hb))]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := 3*a/10) (y := 3*b/10)
    (by positivity) (by linarith [Real.pi_pos]) (by linarith)
  have hs := Real.strictMonoOn_sin.monotoneOn
    (show 3*a/10 ∈ Set.Icc (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
    (show 3*b/10 ∈ Set.Icc (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
    (by linarith : 3*a/10 ≤ 3*b/10)
  have ht := Real.strictMonoOn_tan.monotoneOn
    (show a/2 ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
    (show b/2 ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
    (by linarith : a/2 ≤ b/2)
  have hsn := Real.sin_nonneg_of_nonneg_of_le_pi (x := 3*a/10) (by positivity)
    (by linarith [Real.pi_pos])
  have htn : 0 ≤ Real.tan (b/2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]))
      (hcos _ (ha.trans hab) hb).le
  exact sub_le_sub hc (mul_le_mul ht hs hsn htn)

private def boundRow : Fin 6 → ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  ![(77,79,476,612,305,360,375), (79,81,451,595,351,459,350),
    (81,84,426,578,397,622,330), (84,87,388,552,463,802,290),
    (87,90,349,526,526,1000,250), (90,225/2,310,500,587,1000,230)]

private theorem midpoint_bound_table (i : Fin 6) :
    let (a,b,u,m,c₀,c₁,S) := boundRow i
    0 ≤ a ∧ a ≤ 90 ∧ a ≤ b ∧ b ≤ 225/2 ∧ 0 ≤ u ∧ 0 < c₀ ∧ 0 ≤ S ∧ S ≤ 1000 ∧
    (u/1000)^2 ≤ (m/1000)*(S/1000) ∧
    (1-c₀/1000)*(1-S/1000) ≤ (S/1000)*(1+c₀/1000)^3 ∧
    u/1000 ≤ 1-(1+c₁/1000)*(S/1000) := by
  fin_cases i <;> norm_num [boundRow]

private theorem midpoint_trig_table (i : Fin 6) :
    let (a,b,u,m,c₀,c₁,_) := boundRow i
    Real.cos (degrees (4*a/5)) ≤ u/1000 ∧
    m/1000 ≤ (1 + Real.cos (degrees a))/2 ∧
    c₀/1000 ≤ -Real.cos (degrees (7*a/5)) ∧
    (c₁ = 1000 ∨ (b < 90 ∧
      2*(1-Real.cos (degrees b)) ≤ (1+c₁/1000)*(1+Real.cos (degrees b)))) := by
  have lower a m (h : cosPartial 8 (a * 314160 / 18000000) ≥ 2 * m - 1)
      (ha : 0 ≤ a) (ha' : a ≤ 158) :
      m ≤ (1 + Real.cos (degrees a))/2 := by
    linarith [(cos_degrees a ha ha').1]
  have negUpper a c (h : cosPartial 9 (a * 314159 / 18000000) ≤ -c)
      (ha : 0 ≤ a) (ha' : a ≤ 158) : c ≤ -Real.cos (degrees a) :=
    by linarith [(cos_degrees a ha ha').2]
  have cross b c (h : 2*(1-cosPartial 8 (b * 314160 / 18000000)) ≤
      (1+c)*(1+cosPartial 8 (b * 314160 / 18000000))) (hc : 0 ≤ 1+c)
      (hb : 0 ≤ b) (hb' : b ≤ 158) :
      2*(1-Real.cos (degrees b)) ≤ (1+c)*(1+Real.cos (degrees b)) := by
    have h₀ := (cos_degrees b hb hb').1
    have h₁ := mul_le_mul_of_nonneg_left (add_le_add_left h₀ 1) hc
    linarith
  fin_cases i
  all_goals
    dsimp [boundRow]
    refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (apply le_trans (cos_degrees _ (by norm_num) (by norm_num)).2
       norm_num [cosPartial, cosTerm, Finset.sum_range_succ, Nat.factorial])
    | (rw [show degrees 90 = π/2 by unfold degrees; ring, Real.cos_pi_div_two]
       norm_num)
    | (apply lower <;> norm_num [cosPartial, cosTerm, Finset.sum_range_succ, Nat.factorial])
    | (apply negUpper <;> norm_num [cosPartial, cosTerm, Finset.sum_range_succ, Nat.factorial])
    | (left; norm_num <;> contradiction)
    | (right
       refine ⟨by norm_num, ?_⟩
       apply cross <;> norm_num [cosPartial, cosTerm, Finset.sum_range_succ, Nat.factorial])

private theorem covered_degrees (x : ℝ) (h₀ : 77 ≤ x) (h₁ : x ≤ 225/2) :
    ∃ i : Fin 6, (boundRow i).1 ≤ x ∧ x ≤ (boundRow i).2.1 := by
  by_cases h79 : x ≤ 79
  · exact ⟨0, h₀, h79⟩
  by_cases h81 : x ≤ 81
  · exact ⟨1, le_of_not_ge h79, h81⟩
  by_cases h84 : x ≤ 84
  · exact ⟨2, le_of_not_ge h81, h84⟩
  by_cases h87 : x ≤ 87
  · exact ⟨3, le_of_not_ge h84, h87⟩
  by_cases h90 : x ≤ 90
  · exact ⟨4, le_of_not_ge h87, h90⟩
  exact ⟨5, le_of_not_ge h90, h₁⟩


private theorem arcsin_tan_convex :
    ConvexOn ℝ (Set.Icc 0 (degrees 77 / 2)) (fun x => Real.arcsin (Real.tan x)) := by
  have ht (x : ℝ) (hx : x ∈ Set.Icc 0 (degrees 77 / 2)) :
      x ∈ Set.Ioo (-(π/2)) (π/2) := by
    rcases hx with ⟨h₁, h₂⟩
    unfold degrees at h₂
    constructor <;> linarith [Real.pi_pos]
  have hc (x : ℝ) (hx : x ∈ Set.Icc 0 (degrees 77 / 2)) :
      0 < Real.cos x := Real.cos_pos_of_mem_Ioo (ht x hx)
  have htan (x : ℝ) (hx : x ∈ Set.Icc 0 (degrees 77 / 2)) :
      0 ≤ Real.tan x ∧ Real.tan x < 1 := by
    constructor
    · have h := Real.strictMonoOn_tan.monotoneOn
        (show (0 : ℝ) ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
        (ht x hx) hx.1
      simpa using h
    · have h₂ := hx.2
      unfold degrees at h₂
      have h := Real.strictMonoOn_tan (ht x hx)
        (show π/4 ∈ Set.Ioo (-(π/2)) (π/2) by constructor <;> linarith [Real.pi_pos])
        (show x < π/4 by linarith [Real.pi_pos])
      simpa using h
  have hder (x : ℝ) (hx : x ∈ Set.Icc 0 (degrees 77 / 2)) :
      HasDerivAt (fun y => Real.arcsin (Real.tan y))
        (1 / Real.sqrt (1 - Real.tan x ^ 2) * (1 / Real.cos x ^ 2)) x :=
    (Real.hasDerivAt_arcsin (by linarith [(htan x hx).1]) (htan x hx).2.ne).comp x
      (Real.hasDerivAt_tan (hc x hx).ne')
  apply MonotoneOn.convexOn_of_deriv (convex_Icc ..)
  · exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hder x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hx' := interior_subset hx
    have hy' := interior_subset hy
    rw [(hder x hx').deriv, (hder y hy').deriv]
    have hm := Real.strictMonoOn_tan.monotoneOn (ht x hx') (ht y hy') hxy
    have htsq := pow_le_pow_left₀ (htan x hx').1 hm 2
    have hytan := pow_lt_pow_left₀ (htan y hy').2 (htan y hy').1 (by decide : 2 ≠ 0)
    have hsin := Real.sqrt_le_sqrt (show 1 - Real.tan y ^ 2 ≤ 1 - Real.tan x ^ 2 by linarith)
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hx'.1 (by linarith [(ht y hy').2, Real.pi_pos]) hxy
    apply mul_le_mul
    · exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by simpa using sub_pos.mpr hytan)) hsin
    · exact one_div_le_one_div_of_le (pow_pos (hc y hy') 2)
        (pow_le_pow_left₀ (hc y hy').le hcos 2)
    · positivity
    · positivity

private theorem small_tan_endpoint :
    Real.tan (degrees 77 / 2) ≤ Real.sin ((7/5 : ℝ) * degrees 77 / 2) := by
  have h₀ := (cos_degrees 77 (by norm_num) (by norm_num)).1
  have h₁ := (cos_degrees (7*77/5) (by norm_num) (by norm_num)).2
  norm_num [cosPartial, cosTerm, Finset.sum_range_succ, Nat.factorial] at h₀ h₁
  have hc : 0 < Real.cos (degrees 77 / 2) := Real.cos_pos_of_mem_Ioo (by
    unfold degrees
    constructor <;> linarith [Real.pi_pos])
  have hd : 0 < 1 + Real.cos (degrees 77) := by linarith
  have ht : 0 ≤ Real.tan (degrees 77 / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by unfold degrees; positivity)
      (by unfold degrees; linarith [Real.pi_pos])) hc.le
  have he : 0 ≤ (7/5 : ℝ) * degrees 77 / 2 := by unfold degrees; positivity
  have heπ : (7/5 : ℝ) * degrees 77 / 2 ≤ π := by unfold degrees; linarith [Real.pi_pos]
  apply (sq_le_sq₀ ht (Real.sin_nonneg_of_nonneg_of_le_pi he heπ)).mp
  rw [tan_half_sq _ hc.ne', Real.sin_sq_eq_half_sub, div_le_iff₀ hd,
    show 2 * (7/5 * degrees 77 / 2) = degrees (7*77/5) by unfold degrees; ring]
  have hm : 0 ≤ (1-Real.cos (degrees (7*77/5)))/2 := by linarith [Real.cos_le_one (degrees (7*77/5))]
  nlinarith only [h₀, h₁, mul_nonneg hm (show 0 ≤ Real.cos (degrees 77) - (22/100 : ℝ) by linarith)]

private theorem small_gap {ε D : ℝ} (he : 0 ≤ ε) (hε : ε ≤ degrees 77)
    (hD : 0 ≤ D) (hDπ : D ≤ π) (hgap : Real.sin (D / 2) ≤ Real.tan (ε / 2)) :
    D ≤ 7*ε/5 := by
  let b := degrees 77 / 2
  have hb : 0 < b := by unfold b degrees; positivity
  let weight := ε / 2 / b
  have hweight : 0 ≤ weight := by dsimp [weight]; positivity
  have hweight₁ : weight ≤ 1 := (div_le_one hb).mpr (by dsimp [b]; linarith)
  have hsum : (1-weight)+weight = 1 := by ring
  have hmul : weight * b = ε/2 := div_mul_cancel₀ _ hb.ne'
  have hconv := arcsin_tan_convex.2 (x := (0 : ℝ)) (y := b)
    (by exact ⟨le_rfl, hb.le⟩) (by exact ⟨hb.le, le_rfl⟩)
    (sub_nonneg.mpr hweight₁) hweight hsum
  simp only [smul_eq_mul, hmul, Real.tan_zero, Real.arcsin_zero, mul_zero, zero_add] at hconv
  have hb₅ : Real.arcsin (Real.tan b) ≤ (7/5 : ℝ)*b := by
    have h₁ := Real.monotone_arcsin small_tan_endpoint
    have h₂ : (7/5 : ℝ)*b ∈ Set.Icc (-(π/2)) (π/2) := by
      unfold b degrees
      constructor <;> linarith [Real.pi_pos]
    rw [show (7/5 : ℝ) * degrees 77 / 2 = (7/5 : ℝ) * b by dsimp [b]; ring] at h₁
    change Real.arcsin (Real.tan b) ≤ _ at h₁
    rw [Real.arcsin_sin h₂.1 h₂.2] at h₁
    exact h₁
  have h₁ := Real.monotone_arcsin hgap
  rw [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)] at h₁
  have h₂ := mul_le_mul_of_nonneg_left hb₅ hweight
  rw [show weight * ((7/5 : ℝ)*b) = (7/5)*(weight*b) by ring, hmul] at h₂
  linarith

end RoundQuaternionK4Bounds
