/- GID: D5/S3/Analytic/SeriesInequalities/LorentzCommonGridStability
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/LorentzCommonGridStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint derivative and Hölder control of the actual common-grid Lorentz centers. -/

import D5.S3.Analytic.SeriesInequalities.LorentzWeightedHolderControl
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
The centers use the same initial grid and refinement for every input function.
The bounds concern the highest Hölder seminorm; lower derivative sup norms are
not needed. Both endpoints and a zero seminorm bound are included.

The recurrence and its derivative estimates follow the common-center construction
of Holtz, Nazarov and Peres, *New coins from old, smoothly*, §5 Steps 1–3.
-/

open Finset Polynomial Complex Filter
open scoped BigOperators Topology

noncomputable section

namespace D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability

open LorentzWeightedHolderControl LorentzLocalCoefficientKernel LorentzCoefficientRemainder

private lemma polynomial_smooth (P : ℂ[X]) (r : ℕ) :
    ContDiffOn ℝ r (fun x : ℝ => P.eval (x : ℂ)) (Set.Icc 0 1) := by
  have h : ContDiff ℂ r (fun z : ℂ => P.eval z) := by
    simpa only [coe_aeval_eq_eval] using P.contDiff_aeval (𝕜 := ℂ) r
  exact ((h.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff).contDiffOn

private lemma polynomial_jet (P : ℂ[X]) (j : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDerivWithin j (fun y : ℝ => P.eval (y : ℂ)) (Set.Icc 0 1) x =
      (derivative^[j] P).eval (x : ℂ) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun y hy => ih hy) (ih hx)]
    simpa only [Function.iterate_succ_apply'] using
      ((derivative^[j] P).hasDerivAt (x : ℂ)).comp_ofReal.hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) x hx)

private lemma grid_mem {m i : ℕ} (hm : 0 < m) (hi : i ≤ m) :
    (i : ℝ) / m ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · exact (div_le_one (by exact_mod_cast hm : (0 : ℝ) < m)).mpr (by exact_mod_cast hi)

private lemma operator_polynomial {m : ℕ} (hm : 0 < m) (r : ℕ) (P : ℂ[X]) :
    holderOperator m r (fun x : ℝ => P.eval (x : ℂ)) = lorentzOperator m r P := by
  unfold holderOperator lorentzOperator lorentzJet
  apply sum_congr rfl
  intro j hj
  congr 1
  apply sum_congr rfl
  intro i hi
  dsimp only
  rw [polynomial_jet P j (grid_mem hm (Nat.le_of_lt_succ (mem_range.mp hi)))]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast]

lemma residual_jet {r j : ℕ} (hj : j ≤ r) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1)) (P : ℂ[X]) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    iteratedDerivWithin j (fun y : ℝ => f y - P.eval (y : ℂ)) (Set.Icc 0 1) x =
      iteratedDerivWithin j f (Set.Icc 0 1) x - (derivative^[j] P).eval (x : ℂ) := by
  rw [show (fun y : ℝ => f y - P.eval (y : ℂ)) = f - (fun y : ℝ => P.eval (y : ℂ)) from rfl,
    iteratedDerivWithin_sub hx (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      ((hf.of_le (by exact_mod_cast hj)) x hx) ((polynomial_smooth P j) x hx),
    polynomial_jet P j hx]

lemma operator_residual {m r : ℕ} (hm : 0 < m) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1)) (P : ℂ[X]) :
    holderOperator m r (fun x : ℝ => f x - P.eval (x : ℂ)) =
      holderOperator m r f - lorentzOperator m r P := by
  unfold holderOperator lorentzOperator lorentzJet
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro i hi
  dsimp only
  rw [residual_jet (Nat.le_of_lt_succ (mem_range.mp hj)) hf P
    (grid_mem hm (Nat.le_of_lt_succ (mem_range.mp hi)))]
  simp only [map_sub, sub_mul, Complex.ofReal_div, Complex.ofReal_natCast]

/-- The actual shared-grid recursion, indexed by the number of refinements. -/
def center (τ b r : ℕ) (f : ℝ → ℂ) : ℕ → ℂ[X]
  | 0 => holderOperator τ r f
  | j + 1 => center τ b r f j + holderOperator (τ * b ^ (j + 1)) r
      (fun x : ℝ => f x - (center τ b r f j).eval (x : ℂ))

private lemma center_step {τ b r j : ℕ} {f : ℝ → ℂ}
    (hn : 0 < τ * b ^ (j + 1)) (hf : ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1)) :
    center τ b r f (j + 1) = holderOperator (τ * b ^ (j + 1)) r f +
      (center τ b r f j - lorentzOperator (τ * b ^ (j + 1)) r (center τ b r f j)) := by
  rw [center, operator_residual hn hf]
  abel

private lemma delta_refinement {m b : ℕ} (hm : 0 < m) (hb : 1 ≤ b)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (b : ℝ) * delta (b * m) x ≤ delta m x := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hbR : 1 ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : 0 < (b : ℝ) := by linarith
  have hv : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hs0 := Real.sqrt_nonneg (b : ℝ)
  have hs2 := Real.sq_sqrt hb0.le
  have hsle : Real.sqrt (b : ℝ) ≤ b := by nlinarith
  unfold delta
  rw [mul_max_of_nonneg _ _ hs0]
  apply max_le
  · apply le_trans _ (le_max_left _ _)
    rw [← Real.sqrt_mul hb0.le]
    have he : (b : ℝ) * (x * (1 - x) / (↑(b * m) : ℝ)) = x * (1 - x) / (m : ℝ) := by
      push_cast
      field_simp
    rw [he]
  · apply le_trans _ (le_max_right _ _)
    have he : (b : ℝ) * (1 / (↑(b * m) : ℝ)) = 1 / (m : ℝ) := by
      push_cast
      field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_right hsle (by positivity)

private lemma negative_scale_refinement {m b : ℕ} (hm : 0 < m) (hb : 1 ≤ b)
    {x q : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hq : 0 ≤ q) :
    delta m x ^ (-q) ≤ (b : ℝ) ^ (-q / 2) * delta (b * m) x ^ (-q) := by
  have hb0 : 0 < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  have hmn : 0 < b * m := Nat.mul_pos (by omega) hm
  calc
    _ ≤ (Real.sqrt (b : ℝ) * delta (b * m) x) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos (Real.sqrt_pos.2 hb0) (delta_pos hmn x))
        (delta_refinement hm hb hx) (neg_nonpos.mpr hq)
    _ = _ := by
      rw [Real.mul_rpow (Real.sqrt_nonneg _) (delta_pos hmn x).le,
        Real.sqrt_eq_rpow, ← Real.rpow_mul hb0.le]
      congr 2
      ring

private lemma local_negative_scale {n : ℕ} (hn : 0 < n) {x z A q : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (hq : 0 ≤ q) (hd : |x - z| ≤ A * delta n x) :
    delta n z ^ (-q) ≤ delta n x ^ (-q) * (1 + A) ^ q := by
  have hx0 := delta_pos hn x
  have hz0 := delta_pos hn z
  have hr : delta n x / delta n z ≤ 1 + A :=
    (inverse_delta_comparison hn hx hz).trans (by
      have := (div_le_iff₀ hx0).mpr hd
      linarith)
  calc
    _ = delta n x ^ (-q) * (delta n x / delta n z) ^ q := by
      rw [Real.div_rpow hx0.le hz0.le, Real.rpow_neg hx0.le, Real.rpow_neg hz0.le]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hr hq) (by positivity)


private lemma holder_from_two_scales {n r : ℕ} (hn : 0 < n)
    {θ q t C D L : ℝ} (hθ : 0 < θ) (hq : 0 ≤ q) (hsum : θ + q = 1)
    (ht : 1 ≤ t) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfar : 2 * C * t ^ (-θ) ≤ L) (hnear : D * (1 + t) ^ q * t ^ q ≤ L)
    (P : ℂ[X])
    (hv : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖(derivative^[r] P).eval (x : ℂ)‖ ≤ C * delta n x ^ θ)
    (hd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖(derivative^[r + 1] P).eval (x : ℂ)‖ ≤ D * delta n x ^ (-q)) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      ‖(derivative^[r] P).eval (x : ℂ) - (derivative^[r] P).eval (y : ℂ)‖ ≤
        L * |x - y| ^ θ := by
  have ht0 : 0 < t := by linarith
  have hordered (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
      (hy : y ∈ Set.Icc (0 : ℝ) 1) (hxy : delta n y ≤ delta n x) :
      ‖(derivative^[r] P).eval (x : ℂ) - (derivative^[r] P).eval (y : ℂ)‖ ≤
        L * |x - y| ^ θ := by
    by_cases hzero : x = y
    · simp [hzero, Real.zero_rpow hθ.ne']
    have hh : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hzero)
    have hx0 := delta_pos hn x
    by_cases hclose : |x - y| ≤ t * delta n x
    · have hb (z : ℝ) (hz : z ∈ Set.uIcc x y) :
          ‖(derivative^[r + 1] P).eval (z : ℂ)‖ ≤
            D * delta n x ^ (-q) * (1 + t) ^ q := by
        have hzI := Set.uIcc_subset_Icc hx hy hz
        have hdist0 : |x - z| ≤ |x - y| := by
          simpa only [abs_sub_comm] using Set.abs_sub_left_of_mem_uIcc hz
        have hdist : |x - z| ≤ t * delta n x := hdist0.trans hclose
        exact (hd z hzI).trans (by
          have := mul_le_mul_of_nonneg_left
            (local_negative_scale hn hx hzI hq hdist) hD
          simpa only [mul_assoc] using this)
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z (_ : z ∈ Set.uIcc x y) => by
          simpa only [Function.iterate_succ_apply'] using
            ((derivative^[r] P).hasDerivAt (z : ℂ)).comp_ofReal.hasDerivWithinAt)
        hb (convex_uIcc x y) Set.left_mem_uIcc Set.right_mem_uIcc
      rw [norm_sub_rev, Real.norm_eq_abs, abs_sub_comm y x] at hmvt
      have hscale : delta n x ^ (-q) * |x - y| ≤ t ^ q * |x - y| ^ θ := by
        have hratio := (div_le_iff₀ hx0).mpr hclose
        have hp : |x - y| ^ q * |x - y| ^ θ = |x - y| := by
          rw [← Real.rpow_add hh, show q + θ = 1 by linarith, Real.rpow_one]
        calc
          _ = (|x - y| / delta n x) ^ q * |x - y| ^ θ := by
            rw [Real.div_rpow hh.le hx0.le, Real.rpow_neg hx0.le, div_eq_mul_inv]
            calc
              _ = (delta n x ^ q)⁻¹ * (|x - y| ^ q * |x - y| ^ θ) :=
                congrArg ((delta n x ^ q)⁻¹ * ·) hp.symm
              _ = _ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (by positivity) hratio hq) (by positivity)
      calc
        _ ≤ (D * delta n x ^ (-q) * (1 + t) ^ q) * |x - y| := hmvt
        _ = (D * (1 + t) ^ q) * (delta n x ^ (-q) * |x - y|) := by ring
        _ ≤ (D * (1 + t) ^ q) * (t ^ q * |x - y| ^ θ) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = (D * (1 + t) ^ q * t ^ q) * |x - y| ^ θ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hnear (by positivity)
    · have hdist : delta n x ≤ |x - y| / t :=
        (le_div_iff₀ ht0).mpr (by nlinarith [le_of_not_ge hclose])
      have hpow : delta n x ^ θ ≤ t ^ (-θ) * |x - y| ^ θ := by
        calc
          _ ≤ (|x - y| / t) ^ θ := Real.rpow_le_rpow hx0.le hdist hθ.le
          _ = _ := by rw [Real.div_rpow hh.le ht0.le, Real.rpow_neg ht0.le]; ring
      calc
        _ ≤ ‖(derivative^[r] P).eval (x : ℂ)‖ +
            ‖(derivative^[r] P).eval (y : ℂ)‖ := norm_sub_le _ _
        _ ≤ C * delta n x ^ θ + C * delta n y ^ θ := add_le_add (hv x hx) (hv y hy)
        _ ≤ C * delta n x ^ θ + C * delta n x ^ θ :=
          add_le_add_right (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (delta_pos hn y).le hxy hθ.le) hC) _
        _ = (2 * C) * delta n x ^ θ := by ring
        _ ≤ (2 * C) * (t ^ (-θ) * |x - y| ^ θ) := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (2 * C * t ^ (-θ)) * |x - y| ^ θ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfar (by positivity)
  intro x hx y hy
  rcases le_total (delta n y) (delta n x) with hxy | hyx
  · exact hordered x y hx hy hxy
  · simpa only [norm_sub_rev, abs_sub_comm] using hordered y x hy hx hyx

private lemma small_power (c q ε : ℝ) (hq : 0 < q) (hε : 0 < ε) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ b : ℕ, B ≤ b → c * (b : ℝ) ^ (-q) ≤ ε := by
  have hlim : Tendsto (fun b : ℕ => c * (b : ℝ) ^ (-q)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop hq).comp tendsto_natCast_atTop_atTop)
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  exact ⟨max 2 B, le_max_left _ _, fun b hb => (hB b ((le_max_right _ _).trans hb)).le⟩


/-- One common refinement threshold controls the actual centers at every level.
The constants precede the refinement, initial grid, function and seminorm bound.
In particular the same threshold can be used for any finite family of regularities. -/
theorem common_grid_stability (r : ℕ) (β : ℝ) (hβ : (r : ℝ) < β)
    (hβ1 : β < (r : ℝ) + 1) :
    ∃ B : ℕ, 2 ≤ B ∧ ∃ U V E : ℝ, 0 < U ∧ 0 < V ∧ 0 < E ∧
      ∀ b : ℕ, B ≤ b → ∀ τ : ℕ, 0 < τ →
      ∀ f : ℝ → ℂ, ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1) →
      ∀ H : ℝ, 0 ≤ H →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r f (Set.Icc 0 1) x -
          iteratedDerivWithin r f (Set.Icc 0 1) y‖ ≤ H * |x - y| ^ (β - (r : ℝ))) →
      ∀ j : ℕ,
        (center τ b r f j).natDegree ≤ τ * b ^ j + r ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
          ‖(derivative^[r] (center τ b r f j)).eval (x : ℂ)-
            (derivative^[r] (center τ b r f j)).eval (y : ℂ)‖ ≤
              U * H * |x - y| ^ (β - (r : ℝ))) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖(derivative^[r + 1] (center τ b r f j)).eval (x : ℂ)‖ ≤
            V * H * delta (τ * b ^ j) x ^ (-((r : ℝ) + 1 - β))) ∧
        ∀ ν ≤ r, ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedDerivWithin ν f (Set.Icc 0 1) x-
            (derivative^[ν] (center τ b r f j)).eval (x : ℂ)‖ ≤
              E * H * delta (τ * b ^ j) x ^ (β - (ν : ℝ)) := by
  obtain ⟨K, hK, ha⟩ := holder_derivative_control r β hβ
  obtain ⟨L, hL, hh⟩ := holder_seminorm_control r β hβ hβ1
  let θ := β - (r : ℝ)
  let q := (r : ℝ) + 1 - β
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hsum : θ + q = 1 := by dsimp [θ, q]; ring
  have hexp : β - ((r + 1 : ℕ) : ℝ) = -q := by dsimp [q]; push_cast; ring
  obtain ⟨W, hW, hw⟩ := weighted_lorentz_stability r q hq.le hq1
  let U := 2 * L
  let V := 2 * K
  let E := K * (1 + U)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  obtain ⟨T, hT, hTbound⟩ := small_power (4 * K) θ 1 hθ zero_lt_one
  let t : ℝ := T
  have ht : 1 ≤ t := by dsimp [t]; exact_mod_cast (by omega : 1 ≤ T)
  have hsplit : 4 * K * t ^ (-θ) ≤ 1 := hTbound T le_rfl
  obtain ⟨B₁, hB₁, hb₁⟩ := small_power (1 + W) (q / 2) (1 / 2) (by positivity) (by norm_num)
  obtain ⟨B₂, hB₂, hb₂⟩ := small_power ((1 + W) * V * (1 + t) ^ q * t ^ q) (q / 2) (U / 2)
    (by positivity) (by positivity)
  refine ⟨max B₁ B₂, hB₁.trans (le_max_left _ _), U, V, E, hU, hV, hE, ?_⟩
  intro b hb τ hτ f hf H hH hholder
  have hb0 : 0 < b := by omega
  have hb1 : 1 ≤ b := by omega
  have hbsmall : (1 + W) * (b : ℝ) ^ (-q / 2) ≤ 1 / 2 := by
    simpa only [neg_div] using hb₁ b ((le_max_left _ _).trans hb)
  have hbnear : ((1 + W) * V * (1 + t) ^ q * t ^ q) * (b : ℝ) ^ (-q / 2) ≤ U / 2 := by
    simpa only [neg_div] using hb₂ b ((le_max_right _ _).trans hb)
  have hgridpos (j : ℕ) : 0 < τ * b ^ j := Nat.mul_pos hτ (pow_pos hb0 _)
  intro j
  induction j with
  | zero =>
    simp only [center, pow_zero, mul_one]
    refine ⟨lorentz_degree τ r _, ?_, ?_, ?_⟩
    · intro x hx y hy
      exact (hh f hf H hH hholder τ hτ x hx y hy).trans (by
        have : L ≤ U := by dsimp [U]; linarith
        gcongr)
    · intro x hx
      have h := (ha f hf H hH hholder τ hτ x hx).2
      rw [hexp] at h
      exact h.trans (by
        have : K ≤ V := by dsimp [V]; linarith
        gcongr; exact Real.rpow_nonneg (delta_pos hτ x).le _)
    · intro ν hν x hx
      exact ((ha f hf H hH hholder τ hτ x hx).1 ν hν).trans (by
        have : K ≤ E := by dsimp [E]; nlinarith
        gcongr; exact Real.rpow_nonneg (delta_pos hτ x).le _)
  | succ j ih =>
    rcases ih with ⟨hdegree, hseminorm, hhigh, herror⟩
    let m := τ * b ^ j
    let n := τ * b ^ (j + 1)
    let P := center τ b r f j
    let Ψ := P - lorentzOperator n r P
    let c := (1 + W) * V * (b : ℝ) ^ (-q / 2)
    have hm : 0 < m := hgridpos j
    have hn : 0 < n := hgridpos (j + 1)
    have hnm : b * m = n := by dsimp [m, n]; rw [pow_succ]; ring
    have hmn : m ≤ n := by rw [← hnm]; nlinarith
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hc : c ≤ V / 2 := by
      have h := mul_le_mul_of_nonneg_right hbsmall hV.le
      dsimp [c]
      nlinarith
    have hscaled (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
        ‖(derivative^[r + 1] P).eval (x : ℂ)‖ ≤
          (V * H * (b : ℝ) ^ (-q / 2)) * delta n x ^ (-q) := by
      have hs := negative_scale_refinement hm hb1 hx hq.le
      rw [hnm] at hs
      calc
        _ ≤ V * H * delta m x ^ (-q) := hhigh x hx
        _ ≤ V * H * ((b : ℝ) ^ (-q / 2) * delta n x ^ (-q)) :=
          mul_le_mul_of_nonneg_left hs (mul_nonneg hV.le hH)
        _ = _ := by ring
    have hΨhigh (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
        ‖(derivative^[r + 1] Ψ).eval (x : ℂ)‖ ≤ c * H * delta n x ^ (-q) := by
      have hQ := hw n hn (V * H * (b : ℝ) ^ (-q / 2)) (by positivity) P hscaled x hx
      simp only [Ψ, iterate_derivative_sub, eval_sub]
      calc
        _ ≤ ‖(derivative^[r + 1] P).eval (x : ℂ)‖ +
            ‖(derivative^[r + 1] (lorentzOperator n r P)).eval (x : ℂ)‖ := norm_sub_le _ _
        _ ≤ (V * H * (b : ℝ) ^ (-q / 2)) * delta n x ^ (-q) +
            W * (V * H * (b : ℝ) ^ (-q / 2)) * delta n x ^ (-q) := add_le_add (hscaled x hx) hQ
        _ = _ := by dsimp [c]; ring
    have hPholder : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r (fun z : ℝ => P.eval (z : ℂ)) (Set.Icc 0 1) x-
          iteratedDerivWithin r (fun z : ℝ => P.eval (z : ℂ)) (Set.Icc 0 1) y‖ ≤
            (U * H) * |x - y| ^ (β - (r : ℝ)) := by
      intro x hx y hy
      simpa only [polynomial_jet P r hx, polynomial_jet P r hy] using hseminorm x hx y hy
    have hΨvalue (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
        ‖(derivative^[r] Ψ).eval (x : ℂ)‖ ≤ (K * U * H) * delta n x ^ θ := by
      have h := (ha (fun z : ℝ => P.eval (z : ℂ)) (polynomial_smooth P r)
        (U * H) (by positivity) hPholder n hn x hx).1 r le_rfl
      rw [polynomial_jet P r hx, operator_polynomial hn] at h
      simpa only [Ψ, iterate_derivative_sub, eval_sub, θ, mul_assoc] using h
    have hΨholder : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖(derivative^[r] Ψ).eval (x : ℂ) - (derivative^[r] Ψ).eval (y : ℂ)‖ ≤
          (U * H / 2) * |x - y| ^ θ := by
      apply holder_from_two_scales hn hθ hq.le hsum ht (by positivity) (by positivity)
        (P := Ψ) (C := K * U * H) (D := c * H)
      · calc
          2 * (K * U * H) * t ^ (-θ) = (4 * K * t ^ (-θ)) * (U * H) / 2 := by ring
          _ ≤ 1 * (U * H) / 2 := by gcongr
          _ = _ := by ring
      · calc
          (c * H) * (1 + t) ^ q * t ^ q =
              (((1 + W) * V * (1 + t) ^ q * t ^ q) * (b : ℝ) ^ (-q / 2)) * H := by
                dsimp only [c]
                ring
          _ ≤ (U / 2) * H := mul_le_mul_of_nonneg_right hbnear hH
          _ = U * H / 2 := by ring
      · exact hΨvalue
      · exact hΨhigh
    have hnext : center τ b r f (j + 1) = holderOperator n r f + Ψ := center_step hn hf
    have hres_smooth : ContDiffOn ℝ r (fun x : ℝ => f x - P.eval (x : ℂ)) (Set.Icc 0 1) :=
      hf.sub (polynomial_smooth P r)
    have hres_holder : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDerivWithin r (fun z : ℝ => f z - P.eval (z : ℂ)) (Set.Icc 0 1) x-
          iteratedDerivWithin r (fun z : ℝ => f z - P.eval (z : ℂ)) (Set.Icc 0 1) y‖ ≤
            ((1 + U) * H) * |x - y| ^ (β - (r : ℝ)) := by
      intro x hx y hy
      rw [residual_jet le_rfl hf P hx, residual_jet le_rfl hf P hy]
      have he : (iteratedDerivWithin r f (Set.Icc 0 1) x - (derivative^[r] P).eval (x : ℂ))-
          (iteratedDerivWithin r f (Set.Icc 0 1) y - (derivative^[r] P).eval (y : ℂ)) =
          (iteratedDerivWithin r f (Set.Icc 0 1) x - iteratedDerivWithin r f (Set.Icc 0 1) y)-
          ((derivative^[r] P).eval (x : ℂ) - (derivative^[r] P).eval (y : ℂ)) := by abel
      rw [he]
      calc
        _ ≤ ‖iteratedDerivWithin r f (Set.Icc 0 1) x - iteratedDerivWithin r f (Set.Icc 0 1) y‖ +
            ‖(derivative^[r] P).eval (x : ℂ) - (derivative^[r] P).eval (y : ℂ)‖ := norm_sub_le _ _
        _ ≤ H * |x - y| ^ (β - (r : ℝ)) + U * H * |x - y| ^ (β - (r : ℝ)) :=
          add_le_add (hholder x hx y hy) (hseminorm x hx y hy)
        _ = _ := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [center]
      apply natDegree_add_le_of_degree_le
      · exact hdegree.trans (by change m + r ≤ n + r; omega)
      · exact lorentz_degree n r _
    · intro x hx y hy
      rw [hnext]
      simp only [iterate_map_add, eval_add]
      have he :
          (derivative^[r] (holderOperator n r f)).eval (x : ℂ) +
            (derivative^[r] Ψ).eval (x : ℂ) -
          ((derivative^[r] (holderOperator n r f)).eval (y : ℂ) + (derivative^[r] Ψ).eval (y : ℂ)) =
          ((derivative^[r] (holderOperator n r f)).eval (x : ℂ)-
            (derivative^[r] (holderOperator n r f)).eval (y : ℂ)) +
          ((derivative^[r] Ψ).eval (x : ℂ) - (derivative^[r] Ψ).eval (y : ℂ)) := by abel
      rw [he]
      calc
        _ ≤ ‖(derivative^[r] (holderOperator n r f)).eval (x : ℂ)-
              (derivative^[r] (holderOperator n r f)).eval (y : ℂ)‖ +
            ‖(derivative^[r] Ψ).eval (x : ℂ) - (derivative^[r] Ψ).eval (y : ℂ)‖ := norm_add_le _ _
        _ ≤ L * H * |x - y| ^ θ + (U * H / 2) * |x - y| ^ θ :=
          add_le_add (hh f hf H hH hholder n hn x hx y hy) (hΨholder x hx y hy)
        _ = _ := by dsimp [U, θ]; ring
    · intro x hx
      rw [hnext]
      simp only [iterate_map_add, eval_add]
      have hQ := (ha f hf H hH hholder n hn x hx).2
      rw [hexp] at hQ
      calc
        _ ≤ ‖(derivative^[r + 1] (holderOperator n r f)).eval (x : ℂ)‖ +
            ‖(derivative^[r + 1] Ψ).eval (x : ℂ)‖ := norm_add_le _ _
        _ ≤ K * H * delta n x ^ (-q) + c * H * delta n x ^ (-q) := add_le_add hQ (hΨhigh x hx)
        _ ≤ K * H * delta n x ^ (-q) + (V / 2) * H * delta n x ^ (-q) := by
          gcongr; exact Real.rpow_nonneg (delta_pos hn x).le _
        _ = V * H * delta n x ^ (-q) := by dsimp only [V]; ring
    · intro ν hν x hx
      have h := (ha (fun z : ℝ => f z - P.eval (z : ℂ)) hres_smooth
        ((1 + U) * H) (by positivity) hres_holder n hn x hx).1 ν hν
      rw [residual_jet hν hf P hx] at h
      rw [center]
      simp only [iterate_map_add, eval_add]
      convert h using 1 <;> (try dsimp only [E]) <;> congr 1 <;> ring

end D5.S3.Analytic.SeriesInequalities.LorentzCommonGridStability
