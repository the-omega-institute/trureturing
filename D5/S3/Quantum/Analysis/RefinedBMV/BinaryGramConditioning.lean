/- GID: D5/S3/Quantum/Analysis/RefinedBMV/BinaryGramConditioning
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/BinaryGramConditioning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Optimal uniform conditioning of the binary four-copy Gram block. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumJet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
For the four-slot deficit, the square of the binary off-diagonal coefficient
is strictly below twice the product of the two diagonal coefficients.
The constant is optimal as the degree grows and the smaller spectral value tends to zero.

The strict comparison follows from a coefficientwise certificate for
the cleared discriminant minus a product that vanishes to order ten and is
positive at every positive gap.
-/

noncomputable section

namespace RefinedBMV.ThreeBlockGram

open FourCopyGap (gapDefect)
open RefinedBMV.ThreeBlockGram.ZeroSpectrum
  (fNum jNum gNum root w N C q coefficient_counts root_pow_eight)
open RefinedBMV.ZeroSpectrum (Group evalGroups checkMasks staticCheck nonneg_of_checks)
open private numerators hf hj hg gapDefect_scale
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation

private def lowerTerm (r y : ℝ) : ℝ :=
  (1-r)^2 * (1-y^2)^4 * (1-r*y^2)^4

/--
Coefficients in the variable `p-1`. A row `⟨i,j,cs⟩` has exponential rate
`-(8*i+j*p)` in the coordinate `t = -log r / 8`, with `y = exp (-p*t)`.
The rows for the discriminant alone number 41. Subtracting `lowerTerm` adds
the two rates at `(5,16)` and `(1,0)`.
-/
private def groups : List Group := [
  ⟨6, 16, [(0, 71), (1, 36)]⟩,
  ⟨5, 16, [(0, 2)]⟩,
  ⟨4, 16, [(0, -145), (1, -36)]⟩,
  ⟨6, 14, [(0, -284), (1, -312), (2, -108), (3, -12)]⟩,
  ⟨5, 14, [(0, 860), (1, 936), (2, 324), (3, 36)]⟩,
  ⟨4, 14, [(0, -868), (1, -936), (2, -324), (3, -36)]⟩,
  ⟨3, 14, [(0, 292), (1, 312), (2, 108), (3, 12)]⟩,
  ⟨6, 12, [(0, 570), (1, 912), (2, 528), (3, 132), (4, 12)]⟩,
  ⟨5, 12, [(0, -2884), (1, -4272), (2, -2328), (3, -552), (4, -48)]⟩,
  ⟨4, 12, [(0, 5204), (1, 7344), (2, 3816), (3, 864), (4, 72)]⟩,
  ⟨3, 12, [(0, -4036), (1, -5520), (2, -2760), (3, -600), (4, -48)]⟩,
  ⟨2, 12, [(0, 1146), (1, 1536), (2, 744), (3, 156), (4, 12)]⟩,
  ⟨6, 10, [(0, -860), (1, -1656), (2, -1248), (3, -462), (4, -84), (5, -6)]⟩,
  ⟨5, 10, [(0, 4912), (1, 9192), (2, 6768), (3, 2442), (4, 432), (5, 30)]⟩,
  ⟨4, 10, [(0, -11252), (1, -20520), (2, -14700), (3, -5160), (4, -888), (5, -60)]⟩,
  ⟨3, 10, [(0, 12940), (1, 22968), (2, 15972), (3, 5448), (4, 912), (5, 60)]⟩,
  ⟨2, 10, [(0, -7472), (1, -12864), (2, -8676), (3, -2874), (4, -468), (5, -30)]⟩,
  ⟨1, 10, [(0, 1732), (1, 2880), (2, 1884), (3, 606), (4, 96), (5, 6)]⟩,
  ⟨6, 8, [(0, 575), (1, 1248), (2, 1108), (3, 516), (4, 133), (5, 18), (6, 1)]⟩,
  ⟨5, 8, [(0, -4766), (1, -9324), (2, -7602), (3, -3312), (4, -816), (5, -108), (6, -6)]⟩,
  ⟨4, 8, [(0, 13243), (1, 25632), (2, 20364), (3, 8604), (4, 2067), (5, 270), (6, 15)]⟩,
  ⟨3, 8, [(0, -17960), (1, -35112), (2, -27740), (3, -11616), (4, -2768), (5, -360), (6, -20)]⟩,
  ⟨2, 8, [(0, 13243), (1, 25632), (2, 20364), (3, 8604), (4, 2067), (5, 270), (6, 15)]⟩,
  ⟨1, 8, [(0, -4766), (1, -9324), (2, -7602), (3, -3312), (4, -816), (5, -108), (6, -6)]⟩,
  ⟨0, 8, [(0, 575), (1, 1248), (2, 1108), (3, 516), (4, 133), (5, 18), (6, 1)]⟩,
  ⟨5, 6, [(0, 1732), (1, 2880), (2, 1884), (3, 606), (4, 96), (5, 6)]⟩,
  ⟨4, 6, [(0, -7472), (1, -12864), (2, -8676), (3, -2874), (4, -468), (5, -30)]⟩,
  ⟨3, 6, [(0, 12940), (1, 22968), (2, 15972), (3, 5448), (4, 912), (5, 60)]⟩,
  ⟨2, 6, [(0, -11252), (1, -20520), (2, -14700), (3, -5160), (4, -888), (5, -60)]⟩,
  ⟨1, 6, [(0, 4912), (1, 9192), (2, 6768), (3, 2442), (4, 432), (5, 30)]⟩,
  ⟨0, 6, [(0, -860), (1, -1656), (2, -1248), (3, -462), (4, -84), (5, -6)]⟩,
  ⟨4, 4, [(0, 1146), (1, 1536), (2, 744), (3, 156), (4, 12)]⟩,
  ⟨3, 4, [(0, -4036), (1, -5520), (2, -2760), (3, -600), (4, -48)]⟩,
  ⟨2, 4, [(0, 5204), (1, 7344), (2, 3816), (3, 864), (4, 72)]⟩,
  ⟨1, 4, [(0, -2884), (1, -4272), (2, -2328), (3, -552), (4, -48)]⟩,
  ⟨0, 4, [(0, 570), (1, 912), (2, 528), (3, 132), (4, 12)]⟩,
  ⟨3, 2, [(0, 292), (1, 312), (2, 108), (3, 12)]⟩,
  ⟨2, 2, [(0, -868), (1, -936), (2, -324), (3, -36)]⟩,
  ⟨1, 2, [(0, 860), (1, 936), (2, 324), (3, 36)]⟩,
  ⟨0, 2, [(0, -284), (1, -312), (2, -108), (3, -12)]⟩,
  ⟨2, 0, [(0, -145), (1, -36)]⟩,
  ⟨1, 0, [(0, 2)]⟩,
  ⟨0, 0, [(0, 71), (1, 36)]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem eval_groups (p r y : ℝ) :
    evalGroups (p-1) r y groups =
      36 * (2 * fNum p r y * jNum p r y - (gNum p r y)^2) - lowerTerm r y := by
  simp only [groups, evalGroups, RefinedBMV.ZeroSpectrum.Group.eval,
    RefinedBMV.ZeroSpectrum.Group.weight, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one]
  unfold fNum jNum gNum N C q w lowerTerm
  ring

-- Degree at most 6, affine difference bound 80 and 43 prefix roots.
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 50000 in
private theorem static_checked : staticCheck groups 6 80 320 52 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 50000 in
private theorem masks_checked : checkMasks 320 52 groups = true := by
  decide +kernel

private theorem cleared_q_pos (p : ℕ) (hp : 0 < p) {r : ℝ}
    (hr : 0 < r) (hr₁ : r < 1) :
    0 < 2 * fNum p r (root p r) * jNum p r (root p r) - (gNum p r (root p r))^2 := by
  let t : ℝ := -Real.log r / 8
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have ht : 0 < t := by
    dsimp [t]
    linarith only [Real.log_neg hr hr₁]
  have hb : Real.exp (-8*t) = r := by
    rw [show -8*t = Real.log r by dsimp [t]; ring, Real.exp_log hr]
  have hy : Real.exp (-(p : ℝ)*t) = root p r := by
    rw [root, Real.rpow_def_of_pos hr]
    congr 1
    dsimp [t]
    ring
  have hy₀ : 0 < root p r := by rw [← hy]; exact Real.exp_pos _
  have hy₁ : root p r < 1 := by
    rw [← hy, Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (lt_of_lt_of_le zero_lt_one hp₁)) ht
  have hy₂ : (root p r)^2 < 1 := pow_lt_one₀ hy₀.le hy₁ (by decide)
  have hry₂ : r * (root p r)^2 < 1 :=
    (mul_lt_mul_of_pos_left hy₂ hr).trans (by simpa only [mul_one] using hr₁)
  have hlower : 0 < lowerTerm r (root p r) :=
    mul_pos (mul_pos (pow_pos (sub_pos.mpr hr₁) _) (pow_pos (sub_pos.mpr hy₂) _))
      (pow_pos (sub_pos.mpr hry₂) _)
  have h := nonneg_of_checks groups 6 80 320 52 static_checked masks_checked p t hp₁ ht.le
  rw [hb, hy, eval_groups] at h
  exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 36)).mp
    (hlower.trans_le (sub_nonneg.mp h))

private theorem cleared_deficits (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 ≤ r) :
    (w r)^3 * gapDefect p r r r 1 = fNum p r (root p r) ∧
    (w r)^3 * gapDefect p 1 1 1 r = jNum p r (root p r) ∧
    (w r)^3 * gapDefect p r r 1 1 = gNum p r (root p r) := by
  have hcounts := coefficient_counts p hp hr
  have hnum := numerators p r (root p r) (root_pow_eight p hr)
  refine ⟨?_, ?_, ?_⟩
  · change (w r)^3 * f (spectralDefect p ![0,r,1]) 1 2 = _
    rw [hcounts.f12]
    exact hf hnum
  · change (w r)^3 * f (spectralDefect p ![0,r,1]) 2 1 = _
    rw [hcounts.f21]
    exact hj hnum
  · change (w r)^3 * g (spectralDefect p ![0,r,1]) 1 2 = _
    rw [hcounts.g12]
    exact hg hnum

private theorem cleared_comparison (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 ≤ r)
    (c : ℝ) :
    (gNum p r (root p r))^2 - c * fNum p r (root p r) * jNum p r (root p r) =
      (w r)^6 * ((gapDefect p r r 1 1)^2 -
        c * gapDefect p r r r 1 * gapDefect p 1 1 1 r) := by
  obtain ⟨hF,hJ,hG⟩ := cleared_deficits p hp hr
  rw [← hF, ← hJ, ← hG]
  ring

private theorem normalized_conditioning (p : ℕ) (hp : 0 < p)
    {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    (gapDefect p r r 1 1)^2 < 2 * gapDefect p r r r 1 * gapDefect p 1 1 1 r := by
  have hw : 0 < (w r)^6 := pow_pos (sub_pos.mpr hr₁) _
  apply sub_neg.mp
  refine lt_of_mul_lt_mul_left ?_ hw.le
  rw [mul_zero, ← cleared_comparison p hp hr.le]
  exact sub_neg.mpr (sub_pos.mp (cleared_q_pos p hp hr hr₁))

private theorem conditioning_of_lt (p : ℕ) (hp : 0 < p)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (gapDefect p x x y y)^2 < 2 * gapDefect p x x x y * gapDefect p y y y x := by
  have hy := hx.trans hxy
  let r := x/y
  have hr : 0 < r := div_pos hx hy
  have hr₁ : r < 1 := (div_lt_iff₀ hy).mpr (by simpa only [one_mul] using hxy)
  have hscale : y*r = x := by
    dsimp [r]
    rw [mul_comm, div_mul_cancel₀ _ hy.ne']
  have hF : gapDefect p x x x y = y^p * gapDefect p r r r 1 := by
    simpa only [hscale, mul_one] using
      (gapDefect_scale p hy.le hr.le hr.le hr.le zero_le_one)
  have hJ : gapDefect p y y y x = y^p * gapDefect p 1 1 1 r := by
    simpa only [hscale, mul_one] using
      (gapDefect_scale p hy.le zero_le_one zero_le_one zero_le_one hr.le)
  have hG : gapDefect p x x y y = y^p * gapDefect p r r 1 1 := by
    simpa only [hscale, mul_one] using
      (gapDefect_scale p hy.le hr.le hr.le zero_le_one zero_le_one)
  apply sub_pos.mp
  rw [hF, hJ, hG]
  calc
    0 < (y^p)^2 * (2 * gapDefect p r r r 1 * gapDefect p 1 1 1 r -
        (gapDefect p r r 1 1)^2) :=
      mul_pos (pow_pos (pow_pos hy _) _) (sub_pos.mpr (normalized_conditioning p hp hr hr₁))
    _ = _ := by ring

/-- The strict binary bound in the unnormalized four-slot deficit. -/
private theorem gapDefect_binary_conditioning (p : ℕ) (hp : 0 < p)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    (gapDefect p x x y y)^2 < 2 * gapDefect p x x x y * gapDefect p y y y x := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact conditioning_of_lt p hp hx hlt
  · have hswap : gapDefect p x x y y = gapDefect p y y x x := by
      rw [gapDefect_swap12 p x x y y, gapDefect_swap01 p x y x y,
        gapDefect_swap23 p y x x y, gapDefect_swap12 p y x y x]
    rw [hswap]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using conditioning_of_lt p hp hy hgt

/-- The strict binary bound for the coefficients of the actual spectral Gram block. -/
theorem spectralDefect_binary_conditioning (p : ℕ) (hp : 0 < p)
    (x : Fin 3 → ℝ) (i j : Fin 3) (hi : 0 < x i) (hj : 0 < x j) (hij : x i ≠ x j) :
    (g (spectralDefect p x) i j)^2 <
      2 * f (spectralDefect p x) i j * f (spectralDefect p x) j i :=
  gapDefect_binary_conditioning p hp hi hj hij

/-- Every smaller constant fails for some positive integral degree and
strictly positive unequal spectral values, even with the larger value fixed at one. -/
theorem gapDefect_binary_conditioning_sharp {c : ℝ} (hc : c < 2) :
    ∃ (p : ℕ) (r : ℝ), 0 < p ∧ 0 < r ∧ r < 1 ∧
      c * gapDefect p r r r 1 * gapDefect p 1 1 1 r < (gapDefect p r r 1 1)^2 := by
  have hc' : 0 < 2-c := sub_pos.mpr hc
  obtain ⟨p,hp⟩ := exists_nat_gt (2 / (2-c))
  have hp₀ : (0 : ℝ) < p := (div_pos (by norm_num) hc').trans hp
  have hpₙ : 0 < p := by exact_mod_cast hp₀
  have hpexp : (p : ℝ) / 8 ≠ 0 := (div_pos hp₀ (by norm_num)).ne'
  let E (r : ℝ) :=
    (gNum p r (root p r))^2 - c * fNum p r (root p r) * jNum p r (root p r)
  have hroot : Continuous (root p) := Real.continuous_rpow_const (by positivity)
  have hcont : Continuous E := by
    unfold E gNum fNum jNum N C w
    fun_prop
  have hfactor : 0 < (2 - c) * ((p : ℝ)+2) - 2 := by
    have hmul := (div_lt_iff₀ hc').mp hp
    nlinarith only [hmul, hc']
  have hE₀ : 0 < E 0 := by
    have heq : E 0 = ((p : ℝ)+1)/2 * ((2-c)*((p : ℝ)+2)-2) := by
      simp [E, gNum, fNum, jNum, root, Real.zero_rpow hpexp, N, C, w, q] <;> ring
    rw [heq]
    exact mul_pos (by positivity) hfactor
  have hopen : IsOpen {r : ℝ | 0 < E r} := isOpen_lt continuous_const hcont
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen 0 hE₀
  let r : ℝ := min (ε/2) (1/2)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr₁ : r < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hrε : r < ε := (min_le_left _ _).trans_lt (by linarith only [hε])
  have hEr : 0 < E r := hball (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr] using hrε)
  change 0 < (gNum p r (root p r))^2 - c * fNum p r (root p r) * jNum p r (root p r) at hEr
  rw [cleared_comparison p hpₙ hr.le c] at hEr
  have hw : 0 < (w r)^6 := pow_pos (sub_pos.mpr hr₁) _
  exact ⟨p,r,hpₙ,hr,hr₁,sub_pos.mp ((mul_pos_iff_of_pos_left hw).mp hEr)⟩

#print axioms spectralDefect_binary_conditioning
#print axioms gapDefect_binary_conditioning_sharp

end RefinedBMV.ThreeBlockGram
