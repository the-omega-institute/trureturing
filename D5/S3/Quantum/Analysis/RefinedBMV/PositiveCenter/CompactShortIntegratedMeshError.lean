/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortIntegratedMeshError
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrated Taylor bounds for the refined BMV marginal quadrature errors. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMarginalBoxError

/-! Integrated Taylor bounds for the absolute moments in the short-gap marginal mesh error. -/

open MeasureTheory
open scoped Interval

namespace RefinedBMV.PositiveCenter

private def affineMomentMass {𝕜 : Type*} [Field 𝕜] (L A B : 𝕜) (k : ℕ) : 𝕜 :=
  A * (L ^ (k + 1) / ((k + 1 : ℕ) : 𝕜)) +
    B * (L ^ (k + 2) / ((k + 2 : ℕ) : 𝕜))

private def affineExpMomentBound {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    (L r A B : 𝕜) (m k : ℕ) : 𝕜 :=
  let R := |r * L|
  (∑ n ∈ Finset.range m, r ^ n / (n.factorial : 𝕜) * affineMomentMass L A B (k + n)) +
    (R ^ m / (m.factorial : 𝕜) / (1 - R / (m.succ : 𝕜))) * affineMomentMass L A B k

/-- The exact Taylor upper bound for the moment with affine weight `A + B * x` on
`[-1, 2]`. The two truncation orders belong to the reflected negative and positive halves. -/
def shortExpMomentBound (lo hi A B : ℚ) (mNeg mPos k : ℕ) : ℚ :=
  affineExpMomentBound 1 (-lo) A (-B) mNeg k + affineExpMomentBound 2 hi A B mPos k

private theorem integral_affine_monomial (L A B : ℝ) (k : ℕ) :
    (∫ x in (0 : ℝ)..L, x ^ k * (A + B * x)) = affineMomentMass L A B k := by
  have heq (x : ℝ) : x ^ k * (A + B * x) = A * x ^ k + B * x ^ (k + 1) := by
    rw [pow_succ]
    ring
  have hint (c : ℝ) (n : ℕ) :
      IntervalIntegrable (fun x : ℝ ↦ c * x ^ n) volume 0 L := by
    apply Continuous.intervalIntegrable
    fun_prop
  simp_rw [heq]
  rw [intervalIntegral.integral_add (hint A k) (hint B (k + 1))]
  simp only [intervalIntegral.integral_const_mul, integral_pow, affineMomentMass,
    zero_pow (Nat.succ_ne_zero _), sub_zero]
  simp only [← Nat.cast_succ]

private theorem integral_affine_exp_le {L s r A B : ℝ} {m : ℕ} (k : ℕ)
    (hL : 0 ≤ L) (hs : s ≤ r) (hm : 2 ≤ m) (hr : |r * L| / (m.succ : ℝ) < 1)
    (hw : ∀ x ∈ Set.Icc 0 L, 0 ≤ A + B * x) :
    (∫ x in (0 : ℝ)..L, x ^ k * (A + B * x) * Real.exp (s * x)) ≤
      affineExpMomentBound L r A B m k := by
  let R := |r * L|
  let tail := R ^ m / (m.factorial : ℝ) / (1 - R / (m.succ : ℝ))
  let term (n : ℕ) (x : ℝ) := r ^ n / (n.factorial : ℝ) * (x ^ (k + n) * (A + B * x))
  let rest (x : ℝ) := tail * (x ^ k * (A + B * x))
  have hterm (n : ℕ) : IntervalIntegrable (term n) volume 0 L := by
    apply Continuous.intervalIntegrable
    dsimp [term]
    fun_prop
  have hrest : IntervalIntegrable rest volume 0 L := by
    apply Continuous.intervalIntegrable
    dsimp [rest]
    fun_prop
  have hsum : IntervalIntegrable (fun x ↦ ∑ n ∈ Finset.range m, term n x) volume 0 L := by
    convert IntervalIntegrable.sum (Finset.range m) (fun n _ ↦ hterm n) using 1
    funext x
    simp only [Finset.sum_apply]
  calc
    _ ≤ ∫ x in (0 : ℝ)..L, (∑ n ∈ Finset.range m, term n x) + rest x := by
      refine intervalIntegral.integral_mono_on hL
        (Continuous.intervalIntegrable (by fun_prop) _ _) (hsum.add hrest) ?_
      intro x hx
      have harg : |r * x| ≤ R := by
        simp only [R, abs_mul, abs_of_nonneg hx.1, abs_of_nonneg hL]
        exact mul_le_mul_of_nonneg_left hx.2 (abs_nonneg r)
      have htaylor := compactExp_sub_truncation_geometric_le hm harg hr
      have hexp : Real.exp (s * x) ≤ (∑ n ∈ Finset.range m, (r * x) ^ n / (n.factorial : ℝ)) + tail :=
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs hx.1)).trans
          (sub_le_iff_le_add'.mp ((le_abs_self _).trans htaylor))
      have hweight : 0 ≤ x ^ k * (A + B * x) := mul_nonneg (pow_nonneg hx.1 _) (hw x hx)
      apply (mul_le_mul_of_nonneg_left hexp hweight).trans_eq
      rw [mul_add, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro n _
        simp only [term, mul_pow, pow_add]
        ring
      · dsimp [rest]
        ring
    _ = _ := by
      rw [intervalIntegral.integral_add hsum hrest,
        intervalIntegral.integral_finsetSum (fun n _ ↦ hterm n)]
      simp only [term, rest, intervalIntegral.integral_const_mul, integral_affine_monomial,
        affineExpMomentBound, tail, R]

private theorem shortExpMomentBound_cast (lo hi A B : ℚ) (mNeg mPos k : ℕ) :
    (shortExpMomentBound lo hi A B mNeg mPos k : ℝ) =
      affineExpMomentBound 1 (-(lo : ℝ)) (A : ℝ) (-(B : ℝ)) mNeg k +
        affineExpMomentBound 2 (hi : ℝ) (A : ℝ) (B : ℝ) mPos k := by
  simp [shortExpMomentBound, affineExpMomentBound, affineMomentMass]

/-- Split at zero, taking the lower rate on the reflected negative half and the
upper rate on the positive half. This applies to every natural moment order. -/
theorem shortExpMomentBound_sound {lo hi A B : ℚ} {t : ℝ} {mNeg mPos : ℕ} (k : ℕ)
    (hlo : (lo : ℝ) ≤ t) (hhi : t ≤ (hi : ℝ))
    (hmNeg : 2 ≤ mNeg) (hmPos : 2 ≤ mPos)
    (hrNeg : |(lo : ℝ)| / (mNeg.succ : ℝ) < 1)
    (hrPos : |2 * (hi : ℝ)| / (mPos.succ : ℝ) < 1)
    (hw : ∀ x ∈ Set.Icc (-1 : ℝ) 2, 0 ≤ (A : ℝ) + (B : ℝ) * x) :
    (∫ x in (-1 : ℝ)..2, |x| ^ k * ((A : ℝ) + (B : ℝ) * x) * Real.exp (t * x)) ≤
      (shortExpMomentBound lo hi A B mNeg mPos k : ℝ) := by
  let f (x : ℝ) := |x| ^ k * ((A : ℝ) + (B : ℝ) * x) * Real.exp (t * x)
  have hf : Continuous f := by dsimp [f]; fun_prop
  change (∫ x in (-1 : ℝ)..2, f x) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-1) 0) (hf.intervalIntegrable 0 2), shortExpMomentBound_cast]
  apply add_le_add
  · have hreflect : (∫ x in (0 : ℝ)..1, f (-x)) = ∫ x in (-1 : ℝ)..0, f x := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg (a := 0) (b := 1) (f := f))
    rw [← hreflect]
    calc
      _ = ∫ x in (0 : ℝ)..1, x ^ k * ((A : ℝ) + (-(B : ℝ)) * x) * Real.exp (-t * x) := by
        refine intervalIntegral.integral_congr fun x hx ↦ ?_
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        simp [f, abs_of_nonneg hx.1, mul_neg, neg_mul]
      _ ≤ _ := integral_affine_exp_le k (by norm_num) (neg_le_neg hlo) hmNeg
        (by simpa using hrNeg) (fun x hx ↦ by
          simpa only [neg_mul, mul_neg] using
            hw (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  · calc
      _ = ∫ x in (0 : ℝ)..2, x ^ k * ((A : ℝ) + (B : ℝ) * x) * Real.exp (t * x) := by
        refine intervalIntegral.integral_congr fun x hx ↦ ?_
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
        simp [f, abs_of_nonneg hx.1]
      _ ≤ _ := integral_affine_exp_le k (by norm_num) hhi hmPos
        (by simpa only [mul_comm] using hrPos)
        (fun x hx ↦ hw x ⟨by linarith [hx.1], hx.2⟩)

/-- Bounds for the unweighted moments and the moments with weight `2 + h - x`. -/
theorem shortMarginalExpMoments_le {lo hi H : ℚ} {h t : ℝ} {mNeg mPos : ℕ} (k : ℕ)
    (hlo : (lo : ℝ) ≤ t) (hhi : t ≤ (hi : ℝ)) (hh : 0 ≤ h) (hH : h ≤ (H : ℝ))
    (hmNeg : 2 ≤ mNeg) (hmPos : 2 ≤ mPos)
    (hrNeg : |(lo : ℝ)| / (mNeg.succ : ℝ) < 1)
    (hrPos : |2 * (hi : ℝ)| / (mPos.succ : ℝ) < 1) :
    (∫ x in (-1 : ℝ)..2, |x| ^ k * Real.exp (t * x)) ≤
      (shortExpMomentBound lo hi 1 0 mNeg mPos k : ℝ) ∧
    (∫ x in (-1 : ℝ)..2, |x| ^ k * (2 + h - x) * Real.exp (t * x)) ≤
      (shortExpMomentBound lo hi (2 + H) (-1) mNeg mPos k : ℝ) := by
  have hu := shortExpMomentBound_sound (A := 1) (B := 0) k hlo hhi hmNeg hmPos hrNeg hrPos
    (fun _ _ ↦ by norm_num)
  have hw := shortExpMomentBound_sound (A := 2 + H) (B := -1) k hlo hhi hmNeg hmPos hrNeg hrPos
    (fun x hx ↦ by
      push_cast
      linarith [hx.2])
  refine ⟨by simpa using hu, ?_⟩
  simp only [Rat.cast_add, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one, neg_one_mul,
    ← sub_eq_add_neg] at hw
  refine le_trans (intervalIntegral.integral_mono_on (by norm_num)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) ?_) hw
  intro x _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (abs_nonneg x) k)) (Real.exp_nonneg _)

open D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth (abs_meshRemainder_le meshRemainder)
open CompactTaylorModel (InBox Model)

private def shortMarginalMeshTermBound (H lo hi : ℚ) (mNeg mPos : ℕ)
    (a b : ℚ) (n k : ℕ) : ℚ :=
  let R := max |lo| |hi|
  a * R ^ (n + 1) * shortExpMomentBound lo hi (2 + H) (-1) mNeg mPos k +
    b * R ^ n * shortExpMomentBound lo hi 1 0 mNeg mPos k

/-- Symmetric integrated mesh radius for the scaled marginal and its first two derivatives. -/
def shortMarginalIntegratedMeshError (H lo hi : ℚ) (mNeg mPos : ℕ) (j : Fin 3) : ℚ :=
  let B := shortMarginalMeshTermBound H lo hi mNeg mPos
  H ^ 6 / 15360 * ![B 1 6 3 0, B 4 18 2 0 + B 1 6 3 1,
    B 12 36 1 0 + B 8 36 2 1 + B 1 6 3 2] j

private noncomputable def shortMarginalMeshTerm (h t a b : ℝ) (n k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (t * x) * (x ^ k * (a * t ^ (n + 1) * (2 + h - x) - b * t ^ n))

private theorem shortMarginalMeshTerm_continuous (h t a b : ℝ) (n k : ℕ) :
    Continuous (shortMarginalMeshTerm h t a b n k) := by
  unfold shortMarginalMeshTerm
  fun_prop

private theorem integral_abs_shortMarginalMeshTerm_le
    {H lo hi a b : ℚ} {h t : ℝ} {mNeg mPos : ℕ} (n k : ℕ)
    (ha : 0 ≤ (a : ℝ)) (hb : 0 ≤ (b : ℝ))
    (hlo : (lo : ℝ) ≤ t) (hhi : t ≤ (hi : ℝ)) (hh : 0 ≤ h) (hH : h ≤ (H : ℝ))
    (hmNeg : 2 ≤ mNeg) (hmPos : 2 ≤ mPos)
    (hrNeg : |(lo : ℝ)| / (mNeg.succ : ℝ) < 1)
    (hrPos : |2 * (hi : ℝ)| / (mPos.succ : ℝ) < 1) :
    (∫ x in (-1 : ℝ)..2, |shortMarginalMeshTerm h t (a : ℝ) (b : ℝ) n k x|) ≤
      (shortMarginalMeshTermBound H lo hi mNeg mPos a b n k : ℝ) := by
  let R := max |(lo : ℝ)| |(hi : ℝ)|
  let c := (a : ℝ) * R ^ (n + 1)
  let d := (b : ℝ) * R ^ n
  let e (x : ℝ) := |x| ^ k * Real.exp (t * x)
  let w (x : ℝ) := |x| ^ k * (2 + h - x) * Real.exp (t * x)
  have ht : |t| ≤ R := abs_le.mpr
    ⟨(neg_le_neg ((neg_le_abs (lo : ℝ)).trans (le_max_left _ _))).trans (by simpa using hlo),
      hhi.trans ((le_abs_self _).trans (le_max_right _ _))⟩
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  have he : IntervalIntegrable (fun x ↦ d * e x) volume (-1) 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [e]
    fun_prop
  have hw : IntervalIntegrable (fun x ↦ c * w x) volume (-1) 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [w]
    fun_prop
  have hmajor : ∀ x ∈ Set.Icc (-1 : ℝ) 2,
      |shortMarginalMeshTerm h t (a : ℝ) (b : ℝ) n k x| ≤ c * w x + d * e x := by
    intro x hx
    have hwx : 0 ≤ 2 + h - x := by linarith [hx.2]
    unfold shortMarginalMeshTerm
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp (t * x) * (|x| ^ k * (c * (2 + h - x) + d)) := by
        gcongr
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg ha, abs_of_nonneg hwx]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ht _) ha) hwx
        · rw [abs_mul, abs_pow, abs_of_nonneg hb]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ht _) hb
      _ = _ := by dsimp [w, e]; ring
  obtain ⟨heBound, hwBound⟩ := shortMarginalExpMoments_le k hlo hhi hh hH hmNeg hmPos hrNeg hrPos
  calc
    _ ≤ ∫ x in (-1 : ℝ)..2, c * w x + d * e x :=
      intervalIntegral.integral_mono_on (by norm_num)
        ((shortMarginalMeshTerm_continuous h t a b n k).abs.intervalIntegrable _ _) (hw.add he) hmajor
    _ = c * (∫ x in (-1 : ℝ)..2, w x) + d * (∫ x in (-1 : ℝ)..2, e x) := by
      rw [intervalIntegral.integral_add hw he, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ _ := by
      simpa only [shortMarginalMeshTermBound, Rat.cast_add, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_max, Rat.cast_abs, R, c, d] using
        add_le_add (mul_le_mul_of_nonneg_left hwBound (by positivity : 0 ≤ c))
          (mul_le_mul_of_nonneg_left heBound (by positivity : 0 ≤ d))

private theorem integral_abs_add_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ x in (-1 : ℝ)..2, |f x + g x|) ≤
      (∫ x in (-1 : ℝ)..2, |f x|) + ∫ x in (-1 : ℝ)..2, |g x| := by
  rw [← intervalIntegral.integral_add (hf.abs.intervalIntegrable _ _) (hg.abs.intervalIntegrable _ _)]
  exact intervalIntegral.integral_mono_on (by norm_num) ((hf.add hg).abs.intervalIntegrable _ _)
    ((hf.abs.add hg.abs).intervalIntegrable _ _) (fun x _ ↦ abs_add_le (f x) (g x))

private noncomputable def shortMarginalIntegratedDensity (j : Fin 3) (h t : ℝ) : ℝ → ℝ :=
  let F := shortMarginalMeshTerm h t
  ![F 1 6 3 0, F 4 18 2 0 + F 1 6 3 1, F 12 36 1 0 + F 8 36 2 1 + F 1 6 3 2] j

set_option maxHeartbeats 600000 in
/-- Integrated symmetric error for the actual scaled marginal derivatives in the
closed quadrature. The interval endpoints used in the mesh radius are rational. -/
theorem compactScaledMarginal_integratedMeshError_le {p : ℕ} (hp : 0 < p) {t : ℝ}
    {H lo hi : ℚ} {mNeg mPos : ℕ} (hH : 3 / (p : ℝ) ≤ (H : ℝ))
    (hlo : (lo : ℝ) ≤ t) (hhi : t ≤ (hi : ℝ)) (hmNeg : 2 ≤ mNeg) (hmPos : 2 ≤ mPos)
    (hrNeg : |(lo : ℝ)| / (mNeg.succ : ℝ) < 1)
    (hrPos : |2 * (hi : ℝ)| / (mPos.succ : ℝ) < 1) (j : Fin 3) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    let q (y : ℝ) := (J * compactKappa p) * compactZ p y
    let Q := compactClosedQuadrature h
      (fun x ↦ iteratedDeriv (j : ℕ) (fun y ↦ regularizedMarginalIntegrand h y x) t)
    |iteratedDeriv (j : ℕ) q t - Q| ≤ (shortMarginalIntegratedMeshError H lo hi mNeg mPos j : ℝ) := by
  let h : ℝ := 3 / (p : ℝ)
  let J := (3 + h) * (3 + 2 * h) / 2
  let q (y : ℝ) := (J * compactKappa p) * compactZ p y
  let Q (k : ℕ) := compactClosedQuadrature h
    (fun x ↦ iteratedDeriv k (fun y ↦ regularizedMarginalIntegrand h y x) t)
  let f := shortMarginalIntegratedDensity j h t
  let F := shortMarginalMeshTerm h t
  let B := shortMarginalMeshTermBound H lo hi mNeg mPos
  let C := ![B 1 6 3 0, B 4 18 2 0 + B 1 6 3 1, B 12 36 1 0 + B 8 36 2 1 + B 1 6 3 2] j
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hF := shortMarginalMeshTerm_continuous h t
  have hf : Continuous f := by
    fin_cases j
    · exact hF 1 6 3 0
    · exact (hF 4 18 2 0).add (hF 1 6 3 1)
    · exact ((hF 12 36 1 0).add (hF 8 36 2 1)).add (hF 1 6 3 2)
  have hsplit : iteratedDeriv (j : ℕ) q t = Q j + meshRemainder (-1) h p f := by
    obtain ⟨h0, h1, h2⟩ := compactScaledMarginal_eq_closed_add_remainder hp t
    fin_cases j
    · rw [iteratedDeriv_zero]
      change q t = Q 0 + _
      change q t = Q 0 + meshRemainder (-1) h p
        (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) at h0
      rw [h0]
      congr 2
      funext x
      change t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6) = F 1 6 3 0 x
      simp only [F, shortMarginalMeshTerm, pow_zero, one_mul]
      ring
    · rw [iteratedDeriv_one]
      change deriv q t = Q 1 + _
      change deriv q t = Q 1 + meshRemainder (-1) h p (compactMarginalRemainderFirst h t) at h1
      rw [h1]
      congr 2
      funext x
      change compactMarginalRemainderFirst h t x = F 4 18 2 0 x + F 1 6 3 1 x
      simp only [F, shortMarginalMeshTerm, compactMarginalRemainderFirst, pow_zero, one_mul, pow_one]
      ring
    · change iteratedDeriv 2 q t = Q 2 + _
      change iteratedDeriv 2 q t = Q 2 + meshRemainder (-1) h p
        (compactMarginalRemainderSecond h t) at h2
      rw [h2]
      congr 2
      funext x
      change compactMarginalRemainderSecond h t x = F 12 36 1 0 x + F 8 36 2 1 x + F 1 6 3 2 x
      simp only [F, shortMarginalMeshTerm, compactMarginalRemainderSecond, pow_zero, one_mul, pow_one]
      ring
  have hB (a b : ℚ) (n k : ℕ) (ha : 0 ≤ (a : ℝ)) (hb : 0 ≤ (b : ℝ)) :
      (∫ x in (-1 : ℝ)..2, |F (a : ℝ) (b : ℝ) n k x|) ≤ (B a b n k : ℝ) :=
    integral_abs_shortMarginalMeshTerm_le n k ha hb hlo hhi hh hH hmNeg hmPos hrNeg hrPos
  have hI : (∫ x in (-1 : ℝ)..2, |f x|) ≤ (C : ℝ) := by
    fin_cases j
    · change (∫ x in (-1 : ℝ)..2, |F 1 6 3 0 x|) ≤ (B 1 6 3 0 : ℝ)
      simpa only [Rat.cast_one, Rat.cast_ofNat] using hB 1 6 3 0 (by norm_num) (by norm_num)
    · change (∫ x in (-1 : ℝ)..2, |F 4 18 2 0 x + F 1 6 3 1 x|) ≤
        ((B 4 18 2 0 + B 1 6 3 1 : ℚ) : ℝ)
      rw [Rat.cast_add]
      exact (integral_abs_add_le (hF 4 18 2 0) (hF 1 6 3 1)).trans
        (add_le_add (by simpa only [Rat.cast_ofNat] using hB 4 18 2 0 (by norm_num) (by norm_num))
          (by simpa only [Rat.cast_one, Rat.cast_ofNat] using hB 1 6 3 1 (by norm_num) (by norm_num)))
    · change (∫ x in (-1 : ℝ)..2, |F 12 36 1 0 x + F 8 36 2 1 x + F 1 6 3 2 x|) ≤
        ((B 12 36 1 0 + B 8 36 2 1 + B 1 6 3 2 : ℚ) : ℝ)
      simp only [Rat.cast_add]
      exact (integral_abs_add_le ((hF 12 36 1 0).add (hF 8 36 2 1)) (hF 1 6 3 2)).trans
        (add_le_add ((integral_abs_add_le (hF 12 36 1 0) (hF 8 36 2 1)).trans
          (add_le_add (by simpa only [Rat.cast_ofNat] using hB 12 36 1 0 (by norm_num) (by norm_num))
            (by simpa only [Rat.cast_ofNat] using hB 8 36 2 1 (by norm_num) (by norm_num))))
          (by simpa only [Rat.cast_one, Rat.cast_ofNat] using hB 1 6 3 2 (by norm_num) (by norm_num)))
  have hspan : (-1 : ℝ) + (p : ℝ) * h = 2 := by
    dsimp [h]
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hp.ne')]
    norm_num
  have hmesh := abs_meshRemainder_le (a := -1) (n := p) hh hf
  rw [hspan] at hmesh
  change |iteratedDeriv (j : ℕ) q t - Q j| ≤ ((H ^ 6 / 15360 * C : ℚ) : ℝ)
  rw [hsplit, add_sub_cancel_left, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  exact hmesh.trans (mul_le_mul
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hh hH 6) (by norm_num)) hI
    (intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _))
    (by positivity))

/-- The closed-quadrature model widened by the integrated mesh radius. -/
theorem marginalClosedQuadratureModel_widen_integratedMeshError_sound
    {s t z offset : ℝ} {Hmax center radius width lo hi : ℚ} {terms order p mNeg mPos : ℕ}
    (j : Fin 3) {H X : Model} (hb : InBox s t z) (hp : 0 < p)
    (hH : H.Encloses s t z (3 / (p : ℝ))) (hX : X.Encloses s t z offset)
    (hmax : 3 / (p : ℝ) ≤ (Hmax : ℝ)) (horder : order ≤ terms) (hterms : 3 ≤ terms)
    (hr : |(center : ℝ)| + |offset| ≤ (radius : ℝ)) (hw : |offset| ≤ (width : ℝ))
    (hratio : 2 * (radius : ℝ) < (terms : ℝ) - 2)
    (hlo : (lo : ℝ) ≤ (center : ℝ) + offset) (hhi : (center : ℝ) + offset ≤ (hi : ℝ))
    (hmNeg : 2 ≤ mNeg) (hmPos : 2 ≤ mPos)
    (hrNeg : |(lo : ℝ)| / (mNeg.succ : ℝ) < 1)
    (hrPos : |2 * (hi : ℝ)| / (mPos.succ : ℝ) < 1) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    let q (y : ℝ) := (J * compactKappa p) * compactZ p y
    ((marginalClosedQuadratureModel Hmax radius width center j terms order H X).widen
      (shortMarginalIntegratedMeshError Hmax lo hi mNeg mPos j)).Encloses s t z
      (iteratedDeriv (j : ℕ) q ((center : ℝ) + offset)) :=
  Model.widen_sound
    (marginalClosedQuadratureModel_sound hb hH hX (by positivity) hmax horder hterms hr hw hratio)
    (compactScaledMarginal_integratedMeshError_le hp hmax hlo hhi hmNeg hmPos hrNeg hrPos j)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
/-- All six moment bounds for the direct upper marginal on the first high-spacing subbox.
The interval for `t = v = u + d` is `[77/16, 5]`, and the spacing cap is `3/11`. -/
theorem firstHighSpacing_directUpper_expMoments_le {t h : ℝ}
    (hlo : 77 / 16 ≤ t) (hhi : t ≤ 5) (hh : 0 ≤ h) (hH : h ≤ 3 / 11) (k : Fin 3) :
    (∫ x in (-1 : ℝ)..2, |x| ^ (k : ℕ) * Real.exp (t * x)) ≤
      ((![4405.29927, 7929.60883, 14449.36097] k : ℚ) : ℝ) ∧
    (∫ x in (-1 : ℝ)..2, |x| ^ (k : ℕ) * (2 + h - x) * Real.exp (t * x)) ≤
      ((![2082.51723, 3572.50809, 6266.72673] k : ℚ) : ℝ) := by
  obtain ⟨he, hw⟩ := shortMarginalExpMoments_le (lo := 77 / 16) (hi := 5) (H := 3 / 11)
    (mNeg := 29) (mPos := 46) (k : ℕ)
    (by simpa using hlo) (by simpa using hhi) hh (by simpa using hH)
    (by decide) (by decide) (by norm_num) (by norm_num)
  constructor
  · refine he.trans ?_
    apply Rat.cast_le.mpr
    fin_cases k <;> decide +kernel
  · refine hw.trans ?_
    apply Rat.cast_le.mpr
    fin_cases k <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
/-- Rounded-up mesh errors for the direct upper marginal, uniformly on the first
high-spacing subbox. -/
theorem firstHighSpacing_directUpper_integratedMeshError_le {p : ℕ} (hp : 0 < p)
    (hH : 3 / (p : ℝ) ≤ 3 / 11) {t : ℝ} (hlo : 77 / 16 ≤ t) (hhi : t ≤ 5) (j : Fin 3) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    let q (y : ℝ) := (J * compactKappa p) * compactZ p y
    let Q := compactClosedQuadrature h
      (fun x ↦ iteratedDeriv (j : ℕ) (fun y ↦ regularizedMarginalIntegrand h y x) t)
    |iteratedDeriv (j : ℕ) q t - Q| ≤ ((![0.123385, 0.300152, 0.720144] j : ℚ) : ℝ) := by
  refine (compactScaledMarginal_integratedMeshError_le (H := 3 / 11) (lo := 77 / 16) (hi := 5)
    (mNeg := 29) (mPos := 46) hp (by simpa using hH) (by simpa using hlo) (by simpa using hhi)
    (by decide) (by decide) (by norm_num) (by norm_num) j).trans ?_
  apply Rat.cast_le.mpr
  fin_cases j <;> decide +kernel

end RefinedBMV.PositiveCenter
