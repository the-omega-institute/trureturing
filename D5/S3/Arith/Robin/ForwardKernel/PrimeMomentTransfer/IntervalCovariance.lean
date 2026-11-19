/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/IntervalCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A linear square-sum error bound yields a uniform conditional interval covariance estimate. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TranslationInvariantPrefix

open scoped BigOperators
open Set

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section

def overlap (a b c d : ℝ) : ℝ := max 0 (min b d - max a c)

def intervalSum (K : ℕ → ℕ → ℝ) (H a b c d : ℝ) : ℝ :=
  ∑ i ∈ Finset.Ioc ⌊a * H⌋₊ ⌊b * H⌋₊,
    ∑ j ∈ Finset.Ioc ⌊c * H⌋₊ ⌊d * H⌋₊, K i j

private lemma sum_Ioc_sub_prefix {f : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) :
    (∑ x ∈ Finset.Ioc a b, f x) =
      (∑ x ∈ Finset.Icc 1 b, f x) - ∑ x ∈ Finset.Icc 1 a, f x := by
  have hsplit := Finset.sum_Ioc_consecutive f (Nat.zero_le a) hab
  rw [← Finset.Icc_add_one_left_eq_Ioc 0 a,
    ← Finset.Icc_add_one_left_eq_Ioc 0 b, zero_add] at hsplit
  linarith

private lemma interval_sum_expand {K : ℕ → ℕ → ℝ} {H a b c d : ℝ}
    (hab : ⌊a * H⌋₊ ≤ ⌊b * H⌋₊) (hcd : ⌊c * H⌋₊ ≤ ⌊d * H⌋₊) :
    intervalSum K H a b c d =
      kernelRectSum K ⌊b * H⌋₊ ⌊d * H⌋₊ - kernelRectSum K ⌊a * H⌋₊ ⌊d * H⌋₊ -
        kernelRectSum K ⌊b * H⌋₊ ⌊c * H⌋₊ + kernelRectSum K ⌊a * H⌋₊ ⌊c * H⌋₊ := by
  unfold intervalSum kernelRectSum
  rw [sum_Ioc_sub_prefix hab]
  simp_rw [sum_Ioc_sub_prefix hcd]
  simp_rw [Finset.sum_sub_distrib]
  ring

private def logMoment (x : ℝ) : ℝ := x * Real.log x

private lemma logMoment_scale {H : ℝ} (hH : 0 < H) (k : ℕ) :
    logMoment k = H * logMoment ((k : ℝ) / H) + (k : ℝ) * Real.log H := by
  have h := Real.negMulLog_mul H ((k : ℝ) / H)
  rw [mul_div_cancel₀ _ (ne_of_gt hH)] at h
  simp only [Real.negMulLog, logMoment] at h ⊢
  field_simp at h ⊢
  nlinarith [h]

private lemma logMoment_bounded {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ∈ Icc 0 B → |logMoment x| ≤ C := by
  have hc : Continuous logMoment := by
    change Continuous (fun x : ℝ => x * Real.log x)
    exact Real.continuous_mul_log
  have hb : Bornology.IsBounded (logMoment '' Icc (0 : ℝ) B) :=
    (isCompact_Icc.image hc).isBounded
  rcases (Metric.isBounded_iff.mp hb) with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  · intro x hx
    have hx' : logMoment x ∈ logMoment '' Icc (0 : ℝ) B := ⟨x, hx, rfl⟩
    have h0 : logMoment 0 ∈ logMoment '' Icc (0 : ℝ) B :=
      ⟨0, ⟨le_rfl, hB⟩, rfl⟩
    have hd := hC hx' h0
    have hdx : |logMoment x| ≤ C := by simpa [logMoment, Real.dist_eq] using hd
    exact hdx.trans (le_max_left _ _)

private lemma distance_combination {ma mb nc nd : ℕ} (hab : ma ≤ mb) (hcd : nc ≤ nd) :
    ((Nat.dist mb nd : ℕ) : ℝ) - (Nat.dist ma nd : ℕ) -
        (Nat.dist mb nc : ℕ) + (Nat.dist ma nc : ℕ) =
      -2 * (max 0 (min mb nd - max ma nc) : ℕ) := by
  have hz : (Nat.dist mb nd : ℤ) - (Nat.dist ma nd : ℤ) -
      (Nat.dist mb nc : ℤ) + (Nat.dist ma nc : ℤ) =
      -2 * (max 0 (min mb nd - max ma nc) : ℤ) := by
    by_cases h₁ : mb ≤ nd <;> by_cases h₂ : ma ≤ nd <;>
      by_cases h₃ : mb ≤ nc <;> by_cases h₄ : ma ≤ nc <;>
        simp [Nat.dist, h₁, h₂, h₃, h₄, max_def, min_def] <;> omega
  have hcast : ((max 0 (min mb nd - max ma nc) : ℕ) : ℤ) =
      max 0 ((min mb nd : ℤ) - (max ma nc : ℤ)) := by
    rw [Nat.cast_max, Nat.cast_zero]
    by_cases hq : max ma nc ≤ min mb nd
    · rw [Nat.cast_sub hq, Nat.cast_min, Nat.cast_max]
    · have hq' : min mb nd ≤ max ma nc := le_of_not_ge hq
      have hz' : min mb nd - max ma nc = 0 := Nat.sub_eq_zero_of_le hq'
      rw [hz', Nat.cast_zero]
      simp [Nat.cast_min, Nat.cast_max, hq'] <;> omega
  rw [Nat.cast_min, Nat.cast_max] at hz
  rw [← hcast] at hz
  exact_mod_cast hz

/-- A linear square-sum error bound gives a uniform covariance bound for bounded intervals. -/
theorem interval_covariance_bound :
  ∀ M : ℝ, 1 ≤ M → ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ K : ℕ → ℕ → ℝ,
      (∀ d e, K d e = K e d) →
      (∀ d e t, K (d+t) (e+t) = K d e) →
      (∀ m : ℕ, 1 ≤ m →
        |kernelSquareSum K m + (m : ℝ) * Real.log m| ≤ C₀ * m) →
      ∀ H : ℝ, 1 ≤ H → ∀ a b c d : ℝ,
        0 ≤ a → a ≤ b → b ≤ M → 0 ≤ c → c ≤ d → d ≤ M →
        |intervalSum K H a b c d + H * Real.log H * overlap a b c d| ≤ C * H := by
  intro M hM C₀ hC₀
  obtain ⟨L, hL, hLb⟩ := logMoment_bounded (B := 2 * (M + 1)) (by linarith)
  refine ⟨4 * C₀ * (M + 1) + 2 * L + 4, by positivity, ?_⟩
  intro K hsym htrans hA H hH a b c d ha hab hb hc hcd hd
  have hH0 : 0 ≤ H := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let ma : ℕ := ⌊a * H⌋₊
  let mb : ℕ := ⌊b * H⌋₊
  let nc : ℕ := ⌊c * H⌋₊
  let nd : ℕ := ⌊d * H⌋₊
  have hma : ma ≤ mb := by
    dsimp [ma, mb]
    exact Nat.floor_mono (mul_le_mul_of_nonneg_right hab hH0)
  have hnc : nc ≤ nd := by
    dsimp [nc, nd]
    exact Nat.floor_mono (mul_le_mul_of_nonneg_right hcd hH0)
  have hma0 : (0 : ℝ) ≤ ma := by positivity
  have hb0 : 0 ≤ b := ha.trans hab
  have hd0 : 0 ≤ d := hc.trans hcd
  have hmb : (mb : ℝ) ≤ M * H := by
    dsimp [mb]
    exact (Nat.floor_le (mul_nonneg hb0 hH0)).trans
      (mul_le_mul_of_nonneg_right hb hH0)
  have hnd : (nd : ℝ) ≤ M * H := by
    dsimp [nd]
    exact (Nat.floor_le (mul_nonneg hd0 hH0)).trans
      (mul_le_mul_of_nonneg_right hd hH0)
  have hma' : (ma : ℝ) ≤ M * H := by
    have h : (ma : ℝ) ≤ mb := by exact_mod_cast hma
    exact h.trans hmb
  have hnc' : (nc : ℝ) ≤ M * H := by
    have h : (nc : ℝ) ≤ nd := by exact_mod_cast hnc
    exact h.trans hnd
  have hdist (x y : ℕ) (hx : (x : ℝ) ≤ M * H) (hy : (y : ℝ) ≤ M * H) :
      (Nat.dist x y : ℝ) ≤ 2 * (M + 1) * H := by
    have hd' : Nat.dist x y ≤ x + y := by
      by_cases hxy : x ≤ y
      · rw [Nat.dist_eq_sub_of_le hxy]
        omega
      · rw [Nat.dist_eq_sub_of_le_right (le_of_not_ge hxy)]
        omega
    have hdR : (Nat.dist x y : ℝ) ≤ (x : ℝ) + y := by exact_mod_cast hd'
    nlinarith [hx, hy, hH]
  have hboundA (k : ℕ) :
      |kernelSquareSum K k + logMoment k| ≤ C₀ * k := by
    by_cases hk : k = 0
    · subst k
      simp [kernelSquareSum, kernelRectSum, logMoment]
    · exact hA k (Nat.one_le_iff_ne_zero.mpr hk)
  have hrect (p q : ℕ) :
      2 * kernelRectSum K p q = kernelSquareSum K p + kernelSquareSum K q - kernelSquareSum K (Nat.dist p q) := by
    linarith [prefix_identity K hsym htrans p q]
  have hsum :
      2 * intervalSum K H a b c d =
        - kernelSquareSum K (Nat.dist mb nd) + kernelSquareSum K (Nat.dist ma nd) +
          kernelSquareSum K (Nat.dist mb nc) - kernelSquareSum K (Nat.dist ma nc) := by
    have he := interval_sum_expand (K := K) (H := H) (a := a) (b := b) (c := c) (d := d)
      hma hnc
    rw [he]
    linarith [hrect mb nd, hrect ma nd, hrect mb nc, hrect ma nc]
  let r₁ := Nat.dist mb nd
  let r₂ := Nat.dist ma nd
  let r₃ := Nat.dist mb nc
  let r₄ := Nat.dist ma nc
  let q : ℕ := max 0 (min mb nd - max ma nc)
  have hr₁ : (r₁ : ℝ) ≤ 2 * (M + 1) * H := hdist mb nd hmb hnd
  have hr₂ : (r₂ : ℝ) ≤ 2 * (M + 1) * H := hdist ma nd hma' hnd
  have hr₃ : (r₃ : ℝ) ≤ 2 * (M + 1) * H := hdist mb nc hmb hnc'
  have hr₄ : (r₄ : ℝ) ≤ 2 * (M + 1) * H := hdist ma nc hma' hnc'
  have hratio (r : ℕ) (hr : (r : ℝ) ≤ 2 * (M + 1) * H) :
      (r : ℝ) / H ∈ Icc (0 : ℝ) (2 * (M + 1)) := by
    constructor
    · positivity
    · exact (div_le_iff₀ hHpos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hr)
  have hp₁ := hLb ((r₁ : ℝ) / H) (hratio r₁ hr₁)
  have hp₂ := hLb ((r₂ : ℝ) / H) (hratio r₂ hr₂)
  have hp₃ := hLb ((r₃ : ℝ) / H) (hratio r₃ hr₃)
  have hp₄ := hLb ((r₄ : ℝ) / H) (hratio r₄ hr₄)
  have he₁ := hboundA r₁
  have he₂ := hboundA r₂
  have he₃ := hboundA r₃
  have he₄ := hboundA r₄
  have hqdist := distance_combination hma hnc
  have hlogscale :
      logMoment r₁ - logMoment r₂ - logMoment r₃ + logMoment r₄ +
          2 * H * Real.log H * overlap a b c d =
        H * (logMoment ((r₁ : ℝ) / H) - logMoment ((r₂ : ℝ) / H) -
          logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H)) +
          2 * Real.log H * (H * overlap a b c d - (q : ℝ)) := by
    dsimp [r₁, r₂, r₃, r₄, q] at *
    rw [logMoment_scale hHpos, logMoment_scale hHpos,
      logMoment_scale hHpos, logMoment_scale hHpos]
    ring_nf at hqdist ⊢
    linear_combination (Real.log H) * hqdist
  have hdecomp :
      2 * (intervalSum K H a b c d + H * Real.log H * overlap a b c d) =
        (-(kernelSquareSum K r₁ + logMoment r₁) + (kernelSquareSum K r₂ + logMoment r₂) +
          (kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄)) +
        (logMoment r₁ - logMoment r₂ - logMoment r₃ + logMoment r₄ +
          2 * H * Real.log H * overlap a b c d) := by
    dsimp [r₁, r₂, r₃, r₄]
    linarith [hsum]
  have hmaL : a * H - 1 ≤ (ma : ℝ) := by
    have ht := Nat.lt_floor_add_one (a * H)
    dsimp [ma]
    linarith
  have hmbL : b * H - 1 ≤ (mb : ℝ) := by
    have ht := Nat.lt_floor_add_one (b * H)
    dsimp [mb]
    linarith
  have hncL : c * H - 1 ≤ (nc : ℝ) := by
    have ht := Nat.lt_floor_add_one (c * H)
    dsimp [nc]
    linarith
  have hndL : d * H - 1 ≤ (nd : ℝ) := by
    have ht := Nat.lt_floor_add_one (d * H)
    dsimp [nd]
    linarith
  have hmaU : (ma : ℝ) ≤ a * H := by
    dsimp [ma]
    exact Nat.floor_le (mul_nonneg ha hH0)
  have hmbU : (mb : ℝ) ≤ b * H := by
    dsimp [mb]
    exact Nat.floor_le (mul_nonneg hb0 hH0)
  have hncU : (nc : ℝ) ≤ c * H := by
    dsimp [nc]
    exact Nat.floor_le (mul_nonneg hc hH0)
  have hndU : (nd : ℝ) ≤ d * H := by
    dsimp [nd]
    exact Nat.floor_le (mul_nonneg hd0 hH0)
  have hqrepr : (q : ℝ) =
      max 0 ((min (mb : ℝ) nd) - (max (ma : ℝ) nc)) := by
    dsimp [q]
    by_cases hq : max ma nc ≤ min mb nd
    · rw [Nat.cast_max, Nat.cast_sub hq, Nat.cast_min, Nat.cast_max]
      norm_num
    · have hq' : min mb nd ≤ max ma nc := le_of_not_ge hq
      have hz : min mb nd - max ma nc = 0 := Nat.sub_eq_zero_of_le hq'
      rw [hz, Nat.cast_max]
      simp only [Nat.cast_zero, zero_max]
      have hz' : min (mb : ℝ) (nd : ℝ) ≤ max (ma : ℝ) (nc : ℝ) := by
        exact_mod_cast hq'
      have hz'' : min (mb : ℝ) (nd : ℝ) - max (ma : ℝ) (nc : ℝ) ≤ 0 := by
        linarith
      rw [max_eq_left hz'']
      simp
  have hmin : |(min (mb : ℝ) nd) - min (b * H) (d * H)| ≤ 1 := by
    by_cases hbd : b ≤ d
    · have hmbnd : mb ≤ nd := by
        dsimp [mb, nd]
        exact Nat.floor_mono (mul_le_mul_of_nonneg_right hbd hH0)
      rw [min_eq_left (by exact_mod_cast hmbnd)]
      rw [min_eq_left (mul_le_mul_of_nonneg_right hbd hH0)]
      rw [abs_le]
      constructor <;> linarith [hmbL, hmbU]
    · have hdb : d ≤ b := le_of_not_ge hbd
      have hndmb : nd ≤ mb := by
        dsimp [mb, nd]
        exact Nat.floor_mono (mul_le_mul_of_nonneg_right hdb hH0)
      rw [min_eq_right (by exact_mod_cast hndmb)]
      rw [min_eq_right (mul_le_mul_of_nonneg_right hdb hH0)]
      rw [abs_le]
      constructor <;> linarith [hndL, hndU]
  have hmax : |(max (ma : ℝ) nc) - max (a * H) (c * H)| ≤ 1 := by
    by_cases hac : a ≤ c
    · have hmac : ma ≤ nc := by
        dsimp [ma, nc]
        exact Nat.floor_mono (mul_le_mul_of_nonneg_right hac hH0)
      rw [max_eq_right (by exact_mod_cast hmac)]
      rw [max_eq_right (mul_le_mul_of_nonneg_right hac hH0)]
      rw [abs_le]
      constructor <;> linarith [hncL, hncU]
    · have hca : c ≤ a := le_of_not_ge hac
      have hncma : nc ≤ ma := by
        dsimp [ma, nc]
        exact Nat.floor_mono (mul_le_mul_of_nonneg_right hca hH0)
      rw [max_eq_left (by exact_mod_cast hncma)]
      rw [max_eq_left (mul_le_mul_of_nonneg_right hca hH0)]
      rw [abs_le]
      constructor <;> linarith [hmaL, hmaU]
  have hmax_zero_lip (x y : ℝ) : |max 0 x - max 0 y| ≤ |x - y| := by
    simpa only [max_comm] using (abs_max_sub_max_le_abs x y 0)
  have hoverlap_scale : H * overlap a b c d =
      max 0 (min (b * H) (d * H) - max (a * H) (c * H)) := by
    by_cases hab' : b ≤ d <;> by_cases hac' : a ≤ c
    · have hbdH : b * H ≤ d * H := mul_le_mul_of_nonneg_right hab' hH0
      have hacH : a * H ≤ c * H := mul_le_mul_of_nonneg_right hac' hH0
      rw [overlap, min_eq_left hab', max_eq_right hac', min_eq_left hbdH,
        max_eq_right hacH]
      by_cases h : 0 ≤ b - c
      · have h' : 0 ≤ (b - c) * H := mul_nonneg h hH0
        rw [max_eq_right h]
        rw [show b * H - c * H = (b - c) * H by ring, max_eq_right h']
        ring
      · have h' : (b - c) * H ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hH0
        rw [max_eq_left (le_of_not_ge h)]
        rw [show b * H - c * H = (b - c) * H by ring, max_eq_left h']
        ring
    · have hca' : c ≤ a := le_of_not_ge hac'
      have hbdH : b * H ≤ d * H := mul_le_mul_of_nonneg_right hab' hH0
      have hcaH : c * H ≤ a * H := mul_le_mul_of_nonneg_right hca' hH0
      rw [overlap, min_eq_left hab', max_eq_left hca', min_eq_left hbdH,
        max_eq_left hcaH]
      by_cases h : 0 ≤ b - a
      · have h' : 0 ≤ (b - a) * H := mul_nonneg h hH0
        rw [max_eq_right h]
        rw [show b * H - a * H = (b - a) * H by ring, max_eq_right h']
        ring
      · have h' : (b - a) * H ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hH0
        rw [max_eq_left (le_of_not_ge h)]
        rw [show b * H - a * H = (b - a) * H by ring, max_eq_left h']
        ring
    · have hdb' : d ≤ b := le_of_not_ge hab'
      have hdbH : d * H ≤ b * H := mul_le_mul_of_nonneg_right hdb' hH0
      have hacH : a * H ≤ c * H := mul_le_mul_of_nonneg_right hac' hH0
      rw [overlap, min_eq_right hdb', max_eq_right hac', min_eq_right hdbH,
        max_eq_right hacH]
      by_cases h : 0 ≤ d - c
      · have h' : 0 ≤ (d - c) * H := mul_nonneg h hH0
        rw [max_eq_right h]
        rw [show d * H - c * H = (d - c) * H by ring, max_eq_right h']
        ring
      · have h' : (d - c) * H ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hH0
        rw [max_eq_left (le_of_not_ge h)]
        rw [show d * H - c * H = (d - c) * H by ring, max_eq_left h']
        ring
    · have hca' : c ≤ a := le_of_not_ge hac'
      have hdb' : d ≤ b := le_of_not_ge hab'
      have hdbH : d * H ≤ b * H := mul_le_mul_of_nonneg_right hdb' hH0
      have hcaH : c * H ≤ a * H := mul_le_mul_of_nonneg_right hca' hH0
      rw [overlap, min_eq_right hdb', max_eq_left hca', min_eq_right hdbH,
        max_eq_left hcaH]
      by_cases h : 0 ≤ d - a
      · have h' : 0 ≤ (d - a) * H := mul_nonneg h hH0
        rw [max_eq_right h]
        rw [show d * H - a * H = (d - a) * H by ring, max_eq_right h']
        ring
      · have h' : (d - a) * H ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hH0
        rw [max_eq_left (le_of_not_ge h)]
        rw [show d * H - a * H = (d - a) * H by ring, max_eq_left h']
        ring
  have hdiff : |((min (mb : ℝ) nd) - max (ma : ℝ) nc) -
      (min (b * H) (d * H) - max (a * H) (c * H))| ≤ 2 := by
    have ht : |((min (mb : ℝ) nd) - min (b * H) (d * H)) -
        ((max (ma : ℝ) nc) - max (a * H) (c * H))| ≤
        |(min (mb : ℝ) nd) - min (b * H) (d * H)| +
          |(max (ma : ℝ) nc) - max (a * H) (c * H)| := by
      have heq : ((min (mb : ℝ) nd) - min (b * H) (d * H)) -
          ((max (ma : ℝ) nc) - max (a * H) (c * H)) =
          ((min (mb : ℝ) nd) - min (b * H) (d * H)) +
            (-((max (ma : ℝ) nc) - max (a * H) (c * H))) := by ring
      rw [heq]
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le ((min (mb : ℝ) nd) - min (b * H) (d * H))
          (-((max (ma : ℝ) nc) - max (a * H) (c * H))))
    calc
      _ = |((min (mb : ℝ) nd) - min (b * H) (d * H)) -
          ((max (ma : ℝ) nc) - max (a * H) (c * H))| := by
            congr 1 <;> ring
      _ ≤ |(min (mb : ℝ) nd) - min (b * H) (d * H)| +
          |(max (ma : ℝ) nc) - max (a * H) (c * H)| := ht
      _ ≤ 1 + 1 := add_le_add hmin hmax
      _ = 2 := by norm_num
  have hqerr : |H * overlap a b c d - (q : ℝ)| ≤ 4 := by
    rw [hoverlap_scale, hqrepr]
    calc
      _ ≤ |(min (b * H) (d * H) - max (a * H) (c * H)) -
          (min (mb : ℝ) (nd : ℝ) - max (ma : ℝ) (nc : ℝ))| :=
        hmax_zero_lip _ _
      _ = |min (mb : ℝ) (nd : ℝ) - max (ma : ℝ) (nc : ℝ) -
          (min (b * H) (d * H) - max (a * H) (c * H))| := by
        rw [abs_sub_comm]
      _ ≤ 2 := hdiff
      _ ≤ 4 := by norm_num
  have hlog : |Real.log H| ≤ H := by
    rw [abs_of_nonneg (Real.log_nonneg hH)]
    exact (Real.log_le_sub_one_of_pos hHpos).trans (by linarith)
  have herr :
      |-(kernelSquareSum K r₁ + logMoment r₁) + (kernelSquareSum K r₂ + logMoment r₂) +
          (kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄)| ≤
        8 * C₀ * (M + 1) * H := by
    have ht₁ := abs_add_le (-(kernelSquareSum K r₁ + logMoment r₁))
      ((kernelSquareSum K r₂ + logMoment r₂) + (kernelSquareSum K r₃ + logMoment r₃) -
        (kernelSquareSum K r₄ + logMoment r₄))
    have ht₂ := abs_add_le ((kernelSquareSum K r₂ + logMoment r₂))
      ((kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄))
    have ht₃ := abs_add_le (kernelSquareSum K r₃ + logMoment r₃)
      (-(kernelSquareSum K r₄ + logMoment r₄))
    simp only [abs_neg] at ht₁ ht₂ ht₃ ⊢
    have hb₁ : |kernelSquareSum K r₁ + logMoment r₁| ≤ 2 * C₀ * (M + 1) * H := by
      calc
        _ ≤ C₀ * (r₁ : ℝ) := he₁
        _ ≤ C₀ * (2 * (M + 1) * H) := mul_le_mul_of_nonneg_left hr₁ hC₀
        _ = 2 * C₀ * (M + 1) * H := by ring
    have hb₂ : |kernelSquareSum K r₂ + logMoment r₂| ≤ 2 * C₀ * (M + 1) * H := by
      calc
        _ ≤ C₀ * (r₂ : ℝ) := he₂
        _ ≤ C₀ * (2 * (M + 1) * H) := mul_le_mul_of_nonneg_left hr₂ hC₀
        _ = 2 * C₀ * (M + 1) * H := by ring
    have hb₃ : |kernelSquareSum K r₃ + logMoment r₃| ≤ 2 * C₀ * (M + 1) * H := by
      calc
        _ ≤ C₀ * (r₃ : ℝ) := he₃
        _ ≤ C₀ * (2 * (M + 1) * H) := mul_le_mul_of_nonneg_left hr₃ hC₀
        _ = 2 * C₀ * (M + 1) * H := by ring
    have hb₄ : |kernelSquareSum K r₄ + logMoment r₄| ≤ 2 * C₀ * (M + 1) * H := by
      calc
        _ ≤ C₀ * (r₄ : ℝ) := he₄
        _ ≤ C₀ * (2 * (M + 1) * H) := mul_le_mul_of_nonneg_left hr₄ hC₀
        _ = 2 * C₀ * (M + 1) * H := by ring
    have hb₁' : |-(kernelSquareSum K r₁ + logMoment r₁)| ≤ 2 * C₀ * (M + 1) * H := by
      simpa only [abs_neg] using hb₁
    have hb₄' : |-(kernelSquareSum K r₄ + logMoment r₄)| ≤ 2 * C₀ * (M + 1) * H := by
      simpa only [abs_neg] using hb₄
    have h23 : |(kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄)| ≤
        |kernelSquareSum K r₃ + logMoment r₃| + |kernelSquareSum K r₄ + logMoment r₄| := by
      convert ht₃ using 1 <;> ring
    have hsumabs0 :
        |-(kernelSquareSum K r₁ + logMoment r₁) + (kernelSquareSum K r₂ + logMoment r₂) +
          (kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄)| ≤
          |kernelSquareSum K r₁ + logMoment r₁| + |kernelSquareSum K r₂ + logMoment r₂| +
            |kernelSquareSum K r₃ + logMoment r₃| + |kernelSquareSum K r₄ + logMoment r₄| := by
      calc
        _ = |-(kernelSquareSum K r₁ + logMoment r₁) +
            ((kernelSquareSum K r₂ + logMoment r₂) +
              ((kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄)))| := by
          congr 1 <;> ring
        _ ≤ |kernelSquareSum K r₁ + logMoment r₁| +
            |(kernelSquareSum K r₂ + logMoment r₂) +
              ((kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄))| := by
          convert ht₁ using 1 <;> ring
        _ ≤ |kernelSquareSum K r₁ + logMoment r₁| +
            (|kernelSquareSum K r₂ + logMoment r₂| +
              |(kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄)|) := by
          convert add_le_add_left ht₂ (|kernelSquareSum K r₁ + logMoment r₁|) using 1 <;> ring
        _ ≤ |kernelSquareSum K r₁ + logMoment r₁| +
            (|kernelSquareSum K r₂ + logMoment r₂| +
              (|kernelSquareSum K r₃ + logMoment r₃| + |kernelSquareSum K r₄ + logMoment r₄|)) := by
          convert add_le_add_left
            (add_le_add_left h23 (|kernelSquareSum K r₂ + logMoment r₂|))
            (|kernelSquareSum K r₁ + logMoment r₁|) using 1 <;> ring
        _ = |kernelSquareSum K r₁ + logMoment r₁| + |kernelSquareSum K r₂ + logMoment r₂| +
            |kernelSquareSum K r₃ + logMoment r₃| + |kernelSquareSum K r₄ + logMoment r₄| := by ring
    have hsumabs :
        |-(kernelSquareSum K r₁ + logMoment r₁) + (kernelSquareSum K r₂ + logMoment r₂) +
          (kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄)| ≤
          |-(kernelSquareSum K r₁ + logMoment r₁)| + |kernelSquareSum K r₂ + logMoment r₂| +
            |kernelSquareSum K r₃ + logMoment r₃| + |-(kernelSquareSum K r₄ + logMoment r₄)| := by
      simpa only [abs_neg] using hsumabs0
    linarith [hsumabs, hb₁', hb₂, hb₃, hb₄']
  have hphi :
      |H * (logMoment ((r₁ : ℝ) / H) - logMoment ((r₂ : ℝ) / H) -
        logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H))| ≤ 4 * L * H := by
    have ht₁ := abs_add_le (logMoment ((r₁ : ℝ) / H))
      (-logMoment ((r₂ : ℝ) / H) - logMoment ((r₃ : ℝ) / H) +
        logMoment ((r₄ : ℝ) / H))
    have ht₂ := abs_add_le (-(logMoment ((r₂ : ℝ) / H)))
      (-logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H))
    have ht₃ := abs_add_le (-(logMoment ((r₃ : ℝ) / H)))
      (logMoment ((r₄ : ℝ) / H))
    simp only [abs_neg] at ht₁ ht₂ ht₃
    have h34 : |logMoment ((r₃ : ℝ) / H) - logMoment ((r₄ : ℝ) / H)| ≤
        |logMoment ((r₃ : ℝ) / H)| + |logMoment ((r₄ : ℝ) / H)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (logMoment ((r₃ : ℝ) / H)) (-logMoment ((r₄ : ℝ) / H)))
    have hinner :
        |logMoment ((r₁ : ℝ) / H) - logMoment ((r₂ : ℝ) / H) -
          logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H)| ≤ 4 * L := by
      calc
        _ = |logMoment ((r₁ : ℝ) / H) +
            (-(logMoment ((r₂ : ℝ) / H)) +
              (-(logMoment ((r₃ : ℝ) / H)) + logMoment ((r₄ : ℝ) / H)))| := by
          congr 1 <;> ring
        _ ≤ |logMoment ((r₁ : ℝ) / H)| +
            |-(logMoment ((r₂ : ℝ) / H)) +
              (-(logMoment ((r₃ : ℝ) / H)) + logMoment ((r₄ : ℝ) / H))| := by
          convert ht₁ using 1 <;> ring
        _ ≤ |logMoment ((r₁ : ℝ) / H)| +
            (|logMoment ((r₂ : ℝ) / H)| +
              |-(logMoment ((r₃ : ℝ) / H)) + logMoment ((r₄ : ℝ) / H)|) := by
          convert add_le_add_left ht₂ (|logMoment ((r₁ : ℝ) / H)|) using 1 <;> ring
        _ ≤ |logMoment ((r₁ : ℝ) / H)| +
            (|logMoment ((r₂ : ℝ) / H)| +
              (|logMoment ((r₃ : ℝ) / H)| + |logMoment ((r₄ : ℝ) / H)|)) := by
          convert add_le_add_left (add_le_add_left ht₃ (|logMoment ((r₂ : ℝ) / H)|))
            (|logMoment ((r₁ : ℝ) / H)|) using 1 <;> ring
        _ ≤ 4 * L := by linarith [hp₁, hp₂, hp₃, hp₄]
    rw [abs_mul, abs_of_nonneg hH0]
    calc
      _ ≤ H * (4 * L) := mul_le_mul_of_nonneg_left hinner hH0
      _ = 4 * L * H := by ring
  have hlogterm : |2 * Real.log H * (H * overlap a b c d - (q : ℝ))| ≤ 8 * H := by
    rw [abs_mul, abs_mul]
    have hp : |Real.log H| * |H * overlap a b c d - (q : ℝ)| ≤ H * 4 := by
      exact mul_le_mul hlog hqerr (abs_nonneg _) (by positivity)
    calc
      _ ≤ 2 * (H * 4) := by
        have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
        convert hh using 1 <;> ring
      _ = 8 * H := by ring
  have hcombine :
      2 * |intervalSum K H a b c d + H * Real.log H * overlap a b c d| ≤
        8 * C₀ * (M + 1) * H + 4 * L * H + 8 * H := by
    have heq := hdecomp
    rw [hlogscale] at heq
    have habs := abs_add_le
      (-(kernelSquareSum K r₁ + logMoment r₁) + (kernelSquareSum K r₂ + logMoment r₂) +
        (kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄))
      (H * (logMoment ((r₁ : ℝ) / H) - logMoment ((r₂ : ℝ) / H) -
        logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H)) +
        2 * Real.log H * (H * overlap a b c d - (q : ℝ)))
    have habs' := abs_add_le
      (H * (logMoment ((r₁ : ℝ) / H) - logMoment ((r₂ : ℝ) / H) -
        logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H)))
      (2 * Real.log H * (H * overlap a b c d - (q : ℝ)))
    have habseq := congrArg abs heq
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at habseq
    rw [habseq]
    calc
      _ ≤ |-(kernelSquareSum K r₁ + logMoment r₁) + (kernelSquareSum K r₂ + logMoment r₂) +
            (kernelSquareSum K r₃ + logMoment r₃) - (kernelSquareSum K r₄ + logMoment r₄)| +
          |H * (logMoment ((r₁ : ℝ) / H) - logMoment ((r₂ : ℝ) / H) -
            logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H)) +
            2 * Real.log H * (H * overlap a b c d - (q : ℝ))| := habs
      _ ≤ 8 * C₀ * (M + 1) * H +
          |H * (logMoment ((r₁ : ℝ) / H) - logMoment ((r₂ : ℝ) / H) -
            logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H)) +
            2 * Real.log H * (H * overlap a b c d - (q : ℝ))| :=
        by
          convert add_le_add_right herr
            (|H * (logMoment ((r₁ : ℝ) / H) - logMoment ((r₂ : ℝ) / H) -
              logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H)) +
              2 * Real.log H * (H * overlap a b c d - (q : ℝ))|) using 1 <;> ring
      _ ≤ 8 * C₀ * (M + 1) * H +
          (|H * (logMoment ((r₁ : ℝ) / H) - logMoment ((r₂ : ℝ) / H) -
            logMoment ((r₃ : ℝ) / H) + logMoment ((r₄ : ℝ) / H))| +
            |2 * Real.log H * (H * overlap a b c d - (q : ℝ))|) :=
        by
          convert add_le_add_left habs'
            (8 * C₀ * (M + 1) * H) using 1 <;> ring
      _ ≤ 8 * C₀ * (M + 1) * H + 4 * L * H + 8 * H := by
        convert add_le_add_left (add_le_add hphi hlogterm)
          (8 * C₀ * (M + 1) * H) using 1 <;> ring
  have hhalf := div_le_div_of_nonneg_right hcombine (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ = (2 * |intervalSum K H a b c d + H * Real.log H * overlap a b c d|) / 2 := by ring
    _ ≤ (8 * C₀ * (M + 1) * H + 4 * L * H + 8 * H) / 2 := hhalf
    _ = (4 * C₀ * (M + 1) + 2 * L + 4) * H := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
