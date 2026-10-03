/- GID: D5/S3/Arith/FibonacciAtomic/AffineLcmRobinMargins
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/AffineLcmRobinMargins
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual affine lcm families have positive Robin margins under explicit residue and additive Euler-product estimates. -/
import D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
import D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
import D5.S3.Arith.FibonacciAtomic.AffineLcmCoreArithmetic
/-!
The affine lcm size asymptotic is classical: Qian–Hong, arXiv:1204.5415v2,
Corollary 1.2, specialized to a=3, b=2, l=1 and m=0. The actual-family
valuation, fiber and additive-weight bridges are proved inside the result.
The residue estimates and additive Euler-product limit remain explicit premises.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Topology
open Filter Asymptotics Real Finset MeasureTheory
open D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
open D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
namespace D5.S3.Arith.FibonacciAtomic.AffineLcmRobinMargins
set_option maxHeartbeats 2000000 in
theorem result (C : ℝ) (hC : 0 < C)
    (hTheta1 : (fun y : ℝ => residueTheta 1 y - y / 2) =O[atTop]
      (fun y => y / (log y) ^ 3))
    (hTheta2 : (fun y : ℝ => residueTheta 2 y - y / 2) =O[atTop]
      (fun y => y / (log y) ^ 3))
    (hP : Tendsto (fun y : ℝ => primeProduct y - exp eulerMascheroniConstant * log y)
      atTop (𝓝 0))
 :
  let m : ℕ → ℕ := fun L => 3 * L + 2
  let A : ℕ → ℕ := saturatedCore
  let x : ℕ → ℝ := fun L => (C / 256) * (m L : ℝ) * log (m L)
  let T : ℕ → ℕ := fun L => primeBlock (m L) (x L)
  let H : ℕ → ℕ := fun L => A L * T L
  let E : ℝ := exp eulerMascheroniConstant
  (∀ L : ℕ, 2 ≤ L →
    0 < affineLcm L ∧ 0 < A L ∧ (¬3 ∣ affineLcm L) ∧
    (A L).factorization 3 = Nat.log 3 L ∧
    Nat.lcmUpto L ∣ A L ∧ A L ∣ Nat.lcmUpto (m L) ∧
    visibleCore L (A L) = A L ∧
    (∀ N : ℕ, 0 < N → (shortSignature L N = shortSignature L (A L) ↔
      ∃ t : ℕ, N = A L * t ∧ 1 ≤ t ∧ Nat.Coprime t 3)) ∧
    (∀ N : ℕ, 0 < N → shortSignature L N = shortSignature L (A L) →
      visibleCore L N = A L) ∧
    (16 ≤ L → 5040 ∣ A L) ∧
    (∀ p : ℕ, p.Prime →
      (p ∣ affineLcm L ↔ (p % 3 = 1 ∧ 2 * p ≤ m L) ∨ (p % 3 = 2 ∧ p ≤ m L)))) ∧
  (0 < E * log (3 / (2 * sqrt 2))) ∧ (0 < (E / 2) * log 2) ∧
  Tendsto (fun L : ℕ => log (A L) / ((3 / 4 : ℝ) * (m L))) atTop (𝓝 1) ∧
  Tendsto (fun L : ℕ => log (A L) / ((9 / 4 : ℝ) * (L : ℝ))) atTop (𝓝 1) ∧
  Tendsto (fun L : ℕ => normalizedWeight (A L) -
    E * (log (m L) - log 2 / 2)) atTop (𝓝 0) ∧
  Tendsto (fun L : ℕ => robinMargin (A L)) atTop (𝓝 (E * log (3 / (2 * sqrt 2)))) ∧
  Tendsto (fun L : ℕ => log (H L) / x L) atTop (𝓝 1) ∧
  Tendsto (fun L : ℕ => normalizedWeight (H L) -
    E * (log (x L) - log 2 / 2)) atTop (𝓝 0) ∧
  Tendsto (fun L : ℕ => robinMargin (H L)) atTop (𝓝 ((E / 2) * log 2)) ∧
  Tendsto (fun L : ℕ => (normalizedWeight (H L) / normalizedWeight (A L) - 1) *
    (log L / log (log L))) atTop (𝓝 1) ∧
  Tendsto (fun L : ℕ => (normalizedWeight (H L) - normalizedWeight (A L)) /
    (E * log (log L))) atTop (𝓝 1) ∧
  Tendsto (fun L : ℕ => normalizedWeight (H L) - normalizedWeight (A L)) atTop atTop ∧
  ∀ᶠ L : ℕ in atTop,
    0 < A L ∧ 0 < H L ∧ 5040 < A L ∧ 5040 < H L ∧ 5040 ∣ A L ∧ 5040 ∣ H L ∧
    normalizedWeight (A L) < E * log (log (A L)) ∧
    normalizedWeight (H L) < E * log (log (H L)) ∧
    0 < robinMargin (A L) ∧ 0 < robinMargin (H L) ∧
    (A L : ℝ) ≤ exp (C * (L : ℝ) * log L) ∧
    (H L : ℝ) ≤ exp (C * (L : ℝ) * log L) ∧
    shortSignature L (H L) = shortSignature L (A L) ∧
    visibleCore L (A L) = A L ∧ visibleCore L (H L) = A L ∧
    Nat.Coprime (A L) (T L) ∧ (¬3 ∣ affineLcm L) ∧
    (A L).factorization 3 = Nat.log 3 L ∧
    Nat.lcmUpto L ∣ A L ∧ A L ∣ Nat.lcmUpto (m L) ∧
    (∀ p : ℕ, p.Prime →
      (p ∣ affineLcm L ↔ (p % 3 = 1 ∧ 2 * p ≤ m L) ∨ (p % 3 = 2 ∧ p ≤ m L))) ∧
    (∀ N : ℕ, 0 < N → (shortSignature L N = shortSignature L (A L) ↔
      ∃ t : ℕ, N = A L * t ∧ 1 ≤ t ∧ Nat.Coprime t 3)) ∧
    (∀ N : ℕ, 0 < N → shortSignature L N = shortSignature L (A L) →
      visibleCore L N = A L) := by
  have squares (s : Finset ℕ) (N : ℕ) (hN : 1 ≤ N) (hs : ∀ p ∈ s, N ≤ p) :
      (∑ p ∈ s, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 / (N : ℝ) := by
    have hbase : Summable (fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 2) := by simp
    have hshift : Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + N) ^ 2) := by
      simpa only [Nat.cast_add] using (summable_nat_add_iff N).mpr hbase
    calc
      (∑ p ∈ s, (1 : ℝ) / (p : ℝ) ^ 2) =
          ∑ j ∈ s.image (fun p => p - N), (1 : ℝ) / ((j : ℝ) + N) ^ 2 := by
        rw [Finset.sum_image]
        · apply sum_congr rfl
          intro p hp
          rw [← Nat.cast_add, Nat.sub_add_cancel (hs p hp)]
        · intro p hp q hq heq
          have hpN := hs p hp
          have hqN := hs q hq
          dsimp only at heq
          omega
      _ ≤ ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + N) ^ 2 :=
        Summable.sum_le_tsum _ (fun j _ => by positivity) hshift
      _ ≤ 2 / (N : ℝ) := Mertens.sum_one_div_sq_le (by exact_mod_cast hN)
  have abel (r : ℕ) (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => p.Prime ∧ p % 3 = r),
      (p : ℝ)⁻¹) =
      residueTheta r b / (b * log b) - residueTheta r a / (a * log a) +
        ∫ t in Set.Ioc a b, residueTheta r t * (log t + 1) / (t ^ 2 * (log t) ^ 2) := by
    let c : ℕ → ℝ := fun n => if n.Prime ∧ n % 3 = r then log n else 0
    let f : ℝ → ℝ := fun t => (t * log t)⁻¹
    have positive (t : ℝ) (ht : t ∈ Set.Icc a b) : 0 < t ∧ 0 < log t := by
      have h1 : 1 < t := ha.trans_le ht.1
      exact ⟨by linarith, log_pos h1⟩
    have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :
        HasDerivAt f (-(log t + 1) / (t ^ 2 * (log t) ^ 2)) t := by
      have ht0 := (positive t ht).1.ne'
      have hlt0 := (positive t ht).2.ne'
      have h := ((hasDerivAt_id t).mul (hasDerivAt_log ht0)).inv (mul_ne_zero ht0 hlt0)
      convert h using 1 <;> first
      | rfl
      | (simp [f, ht0, hlt0, pow_two, mul_inv_rev] <;> ring)
    have hlog : ContinuousOn log (Set.Icc a b) :=
      continuousOn_id.log (fun t ht => (positive t ht).1.ne')
    have hk : ContinuousOn (fun t : ℝ => -(log t + 1) / (t ^ 2 * (log t) ^ 2))
        (Set.Icc a b) := by
      apply (hlog.add continuousOn_const).neg.div (continuousOn_id.pow 2 |>.mul (hlog.pow 2))
      intro t ht
      exact mul_ne_zero (pow_ne_zero _ (positive t ht).1.ne')
        (pow_ne_zero _ (positive t ht).2.ne')
    have hderiv : ∀ t ∈ Set.Icc a b,
        deriv f t = -(log t + 1) / (t ^ 2 * (log t) ^ 2) := fun t ht => (hd t ht).deriv
    have hfi : IntegrableOn (deriv f) (Set.Icc a b) :=
      (hk.congr (fun t ht => hderiv t ht)).integrableOn_Icc
    have hsum (y : ℝ) : (∑ n ∈ Icc 0 ⌊y⌋₊, c n) = residueTheta r y := by
      rw [residueTheta, sum_filter, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
      simp [c]
    have hsumBand :
        (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
          ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun p => p.Prime ∧ p % 3 = r), (p : ℝ)⁻¹ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      by_cases hpr : p.Prime ∧ p % 3 = r
      · have hp1 : (1 : ℝ) < p := by exact_mod_cast hpr.1.one_lt
        have hp0 : (p : ℝ) ≠ 0 := by positivity
        have hlogp : log (p : ℝ) ≠ 0 := (log_pos hp1).ne'
        simp [c, hpr, f, mul_inv_rev, hp0, hlogp]
        field_simp [hlogp]
      · simp [c, hpr]
    have hAbel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) c (f := f)
      (by linarith : 0 ≤ a) hab (fun t ht => (hd t ht).differentiableAt) hfi
    rw [hsumBand, hsum b, hsum a] at hAbel
    have hi : (∫ t in Set.Ioc a b, deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) =
        -(∫ t in Set.Ioc a b, residueTheta r t * (log t + 1) / (t ^ 2 * (log t) ^ 2)) := by
      rw [← integral_neg]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change deriv f t * (∑ n ∈ Icc 0 ⌊t⌋₊, c n) =
        -(residueTheta r t * (log t + 1) / (t ^ 2 * log t ^ 2))
      rw [hderiv t ⟨ht.1.le, ht.2⟩, hsum t]
      ring
    rw [hi] at hAbel
    simpa only [f, div_eq_mul_inv, sub_neg_eq_add, mul_comm] using hAbel
  let m : ℕ → ℕ := fun L => 3 * L + 2
  let A : ℕ → ℕ := saturatedCore
  let x : ℕ → ℝ := fun L => (C / 256) * (m L : ℝ) * log (m L)
  let T : ℕ → ℕ := fun L => primeBlock (m L) (x L)
  let H : ℕ → ℕ := fun L => A L * T L
  let E : ℝ := exp eulerMascheroniConstant
  have dyadic (a K : ℝ) (ha : 1 < a) (hla : 1 ≤ log a) (hK : 0 ≤ K)
      (hR : ∀ u ∈ Set.Icc a (2 * a),
        |residueTheta 1 u - u / 2| ≤ K * u / (log u) ^ 3) :
      |(∑ p ∈ (Ioc ⌊a⌋₊ ⌊2 * a⌋₊).filter (fun p => p.Prime ∧ p % 3 = 1),
        (p : ℝ)⁻¹) - (log (log (2 * a)) - log (log a)) / 2| ≤
          4 * K / (log a) ^ 4 := by
    let k : ℝ → ℝ := fun u => (log u + 1) / (u ^ 2 * (log u) ^ 2)
    let R : ℝ → ℝ := fun u => residueTheta 1 u - u / 2
    have ha0 : 0 < a := by linarith
    have hab : a ≤ 2 * a := by linarith
    have positive (u : ℝ) (hu : u ∈ Set.Icc a (2 * a)) :
        0 < u ∧ 0 < log u ∧ log a ≤ log u := by
      have hu0 : 0 < u := ha0.trans_le hu.1
      have hlu := Real.log_le_log ha0 hu.1
      exact ⟨hu0, by linarith, hlu⟩
    have hk : ContinuousOn k (Set.Icc a (2 * a)) := by
      have hl : ContinuousOn log (Set.Icc a (2 * a)) :=
        continuousOn_id.log (fun u hu => (positive u hu).1.ne')
      exact (hl.add continuousOn_const).div
        (continuousOn_id.pow 2 |>.mul (hl.pow 2))
        (fun u hu => mul_ne_zero (pow_ne_zero _ (positive u hu).1.ne')
          (pow_ne_zero _ (positive u hu).2.1.ne'))
    have hmain : ContinuousOn (fun u : ℝ => (u / 2) * k u) (Set.Icc a (2 * a)) := (continuousOn_id.div_const 2).mul hk
    let c : ℕ → ℝ := fun n => if n.Prime ∧ n % 3 = 1 then log n else 0
    have hsum (y : ℝ) : (∑ n ∈ Icc 0 ⌊y⌋₊, c n) = residueTheta 1 y := by
      rw [residueTheta, sum_filter, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
      simp [c]
    have htheta : IntegrableOn (fun u => residueTheta 1 u * k u) (Set.Icc a (2 * a)) := by
      have hi := integrableOn_mul_sum_Icc (m := 0) c ha0.le hk.integrableOn_Icc
      exact hi.congr_fun (fun u _ => by
        change k u * (∑ n ∈ Icc 0 ⌊u⌋₊, c n) = _
        rw [hsum]
        ring) measurableSet_Icc
    have hri : IntegrableOn (fun u => R u * k u) (Set.Icc a (2 * a)) := by
      convert htheta.sub hmain.integrableOn_Icc using 1
      ext u
      dsimp [R]
      ring
    have hderiv (u : ℝ) (hu : u ∈ Set.Icc a (2 * a)) :
        HasDerivAt (fun u : ℝ => (log (log u) - (log u)⁻¹) / 2)
          ((u / 2) * k u) u := by
      have hu0 := (positive u hu).1.ne'
      have hlu0 := (positive u hu).2.1.ne'
      have hd := (((hasDerivAt_log hu0).log hlu0).sub
        ((hasDerivAt_log hu0).inv hlu0)).div_const 2
      convert hd using 1 <;> first
      | rfl
      | (dsimp only [k]; field_simp [hu0, hlu0] <;> ring)
    have hmi : (∫ u in Set.Ioc a (2 * a), (u / 2) * k u) =
        (log (log (2 * a)) - (log (2 * a))⁻¹ -
          (log (log a) - (log a)⁻¹)) / 2 := by
      rw [← intervalIntegral.integral_of_le hab]
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := 2 * a)
        (fun u hu => hderiv u (by simpa [Set.uIcc_of_le hab] using hu))
        (hmain.intervalIntegrable_of_Icc hab)
      convert hi using 1 <;> ring
    have hsplit : (∫ u in Set.Ioc a (2 * a), residueTheta 1 u * k u) =
        (∫ u in Set.Ioc a (2 * a), R u * k u) +
          (∫ u in Set.Ioc a (2 * a), (u / 2) * k u) := by
      rw [← integral_add (hri.mono_set Set.Ioc_subset_Icc_self)
        (hmain.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u _
      dsimp [R]
      ring
    have hboundary (u : ℝ) (hu : u ∈ Set.Icc a (2 * a)) :
        |R u / (u * log u)| ≤ K / (log a) ^ 4 := by
      have hp := positive u hu
      have hr := hR u hu
      rw [abs_div, abs_of_pos (mul_pos hp.1 hp.2.1)]
      calc
        _ ≤ (K * u / log u ^ 3) / (u * log u) :=
          div_le_div_of_nonneg_right hr (mul_pos hp.1 hp.2.1).le
        _ = K / log u ^ 4 := by field_simp [hp.1.ne', hp.2.1.ne'] <;> ring
        _ ≤ K / log a ^ 4 :=
          div_le_div_of_nonneg_left hK (by positivity)
            (pow_le_pow_left₀ (by linarith : 0 ≤ log a) hp.2.2 4)
    have hpoint (u : ℝ) (hu : u ∈ Set.Ioc a (2 * a)) :
        ‖R u * k u‖ ≤ 2 * K / (a * log a ^ 4) := by
      have hc : u ∈ Set.Icc a (2 * a) := ⟨hu.1.le, hu.2⟩
      have hp := positive u hc
      have hu0 : 0 < u := hp.1
      have hlu0 : 0 < log u := hp.2.1
      have hkpos : 0 ≤ k u := by dsimp [k]; positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hkpos]
      calc
        _ ≤ (K * u / log u ^ 3) * k u :=
          mul_le_mul_of_nonneg_right (hR u hc) hkpos
        _ = K * (log u + 1) / (u * log u ^ 5) := by
          dsimp [k]
          field_simp [hu0.ne', hlu0.ne']
          <;> ring
        _ ≤ 2 * K / (u * log u ^ 4) := by
          have hl1 : 1 ≤ log u := hla.trans hp.2.2
          have hfac : K * (log u + 1) ≤ 2 * K * log u := by nlinarith
          calc
            _ ≤ (2 * K * log u) / (u * log u ^ 5) :=
              div_le_div_of_nonneg_right hfac (by positivity)
            _ = _ := by field_simp [hu0.ne', hlu0.ne'] <;> ring
        _ ≤ 2 * K / (a * log a ^ 4) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul hc.1
            (pow_le_pow_left₀ (by linarith : 0 ≤ log a) hp.2.2 4)
            (by positivity) hp.1.le
    have hint : |∫ u in Set.Ioc a (2 * a), R u * k u| ≤ 2 * K / log a ^ 4 := by
      rw [← intervalIntegral.integral_of_le hab]
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := 2 * a)
        (fun u hu => hpoint u (by simpa [Set.uIoc_of_le hab] using hu))
      rw [Real.norm_eq_abs, show 2 * a - a = a by ring, abs_of_pos ha0] at hh
      convert hh using 1 <;> field_simp [ha0.ne'] <;> ring
    have heq := abel 1 a (2 * a) ha hab
    have hKernel : (∫ u in Set.Ioc a (2 * a),
        residueTheta 1 u * (log u + 1) / (u ^ 2 * log u ^ 2)) =
        ∫ u in Set.Ioc a (2 * a), residueTheta 1 u * k u := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u _
      dsimp [k]
      ring
    rw [hKernel] at heq
    rw [hsplit, hmi] at heq
    have hdiff :
        (∑ p ∈ (Ioc ⌊a⌋₊ ⌊2 * a⌋₊).filter (fun p => p.Prime ∧ p % 3 = 1),
          (p : ℝ)⁻¹) - (log (log (2 * a)) - log (log a)) / 2 =
        R (2 * a) / ((2 * a) * log (2 * a)) - R a / (a * log a) +
          ∫ u in Set.Ioc a (2 * a), R u * k u := by
      rw [heq]
      dsimp [R]
      have hlb := (positive (2 * a) ⟨hab, le_rfl⟩).2.1.ne'
      have hla0 : log a ≠ 0 := by linarith
      field_simp [ha0.ne', hla0, hlb]
      <;> ring
    rw [hdiff]
    calc
      _ ≤ |R (2 * a) / ((2 * a) * log (2 * a))| + |R a / (a * log a)| +
          |∫ u in Set.Ioc a (2 * a), R u * k u| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ K / log a ^ 4 + K / log a ^ 4 + 2 * K / log a ^ 4 :=
        add_le_add (add_le_add (hboundary _ ⟨hab, le_rfl⟩)
          (hboundary _ ⟨le_rfl, hab⟩)) hint
      _ = 4 * K / log a ^ 4 := by ring
  have bandCorrection (M : ℕ) (hM : 2 ≤ M) :
      let missing := ((Ioc 0 M).filter Nat.Prime).filter
        (fun p => p % 3 = 1 ∧ M < 2 * p)
      |(∑ p ∈ missing, -log (1 - (p : ℝ)⁻¹)) -
        (∑ p ∈ missing, (p : ℝ)⁻¹)| ≤ 8 / (M : ℝ) := by
    let s := ((Ioc 0 M).filter Nat.Prime).filter
      (fun p => p % 3 = 1 ∧ M < 2 * p)
    let N := ⌊(M : ℝ) / 2⌋₊ + 1
    have hM0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hN0 : 0 < (N : ℝ) := by dsimp [N]; positivity
    have hN (p : ℕ) (hp : p ∈ s) : N ≤ p := by
      have hpm := (mem_filter.mp hp).2.2
      have hpmr : (M : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hpm
      have hpr : (M : ℝ) / 2 < p := by linarith
      have hf : ⌊(M : ℝ) / 2⌋₊ < p :=
        (Nat.floor_lt (by positivity)).mpr hpr
      dsimp [N]
      omega
    have hsq := squares s N (by dsimp [N]; omega) hN
    have hscalar (p : ℕ) (hp : p ∈ s) :
        |(-log (1 - (p : ℝ)⁻¹)) - (p : ℝ)⁻¹| ≤ 2 / (p : ℝ) ^ 2 := by
      have hprime := (mem_filter.mp (mem_filter.mp hp).1).2
      have hmert := Mertens.M_eq_summand_bound p
      rw [show (-log (1 - (p : ℝ)⁻¹)) - (p : ℝ)⁻¹ =
        -(log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) by ring, abs_neg]
      simpa only [Mertens.M_eq_summand, if_pos hprime, one_div] using hmert
    change |(∑ p ∈ s, -log (1 - (p : ℝ)⁻¹)) -
      (∑ p ∈ s, (p : ℝ)⁻¹)| ≤ _
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ s, |(-log (1 - (p : ℝ)⁻¹)) - (p : ℝ)⁻¹| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ s, 2 / (p : ℝ) ^ 2 := sum_le_sum hscalar
      _ = 2 * ∑ p ∈ s, (1 : ℝ) / (p : ℝ) ^ 2 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p _
        ring
      _ ≤ 2 * (2 / (N : ℝ)) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ ≤ 8 / (M : ℝ) := by
        have hf : (M : ℝ) / 2 < (N : ℝ) := by
          simpa [N, Nat.cast_add] using Nat.lt_floor_add_one ((M : ℝ) / 2)
        have heq : 2 * (2 / (N : ℝ)) = 4 / (N : ℝ) := by ring
        rw [heq, div_le_div_iff₀ hN0 hM0]
        nlinarith
  have hE : 0 < E := exp_pos _
  have hκ : 0 < C / 256 := by positivity
  have hmpos (L : ℕ) : 0 < (m L : ℝ) := by
    dsimp [m]
    positivity
  have hmlog (L : ℕ) : 0 < log (m L) := by
    apply log_pos
    dsimp [m]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  have hxpos (L : ℕ) : 0 < x L := mul_pos (mul_pos hκ (hmpos L)) (hmlog L)
  have hnat : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hm : Tendsto (fun L : ℕ => (m L : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hnat
    exact Eventually.of_forall (fun L => by dsimp [m]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) L])
  have hlogL : Tendsto (fun L : ℕ => log L) atTop atTop := tendsto_log_atTop.comp hnat
  have hloglogL : Tendsto (fun L : ℕ => log (log L)) atTop atTop := tendsto_log_atTop.comp hlogL
  have hlogm : Tendsto (fun L : ℕ => log (m L)) atTop atTop := tendsto_log_atTop.comp hm
  have hloglogm : Tendsto (fun L : ℕ => log (log (m L))) atTop atTop := tendsto_log_atTop.comp hlogm
  have hmL : Tendsto (fun L : ℕ => (m L : ℝ) / L) atTop (𝓝 3) := by
    have ht := (hnat.const_div_atTop 2).const_add 3
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    dsimp [m]
    push_cast
    field_simp
  have hlogmL : Tendsto (fun L : ℕ => log (m L) / log L) atTop (𝓝 1) := by
    have ht := ((hmL.log (by norm_num : (3 : ℝ) ≠ 0)).div_atTop hlogL).add_const 1
    simp only [zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ), hlogL.eventually_gt_atTop 0] with L hL hl
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    rw [log_div (hmpos L).ne' hL0]
    field_simp <;> ring
  have hloglogmL : Tendsto (fun L : ℕ => log (log (m L)) / log (log L)) atTop (𝓝 1) := by
    have ht := ((hlogmL.log one_ne_zero).div_atTop hloglogL).add_const 1
    simp only [zero_add] at ht
    apply ht.congr'
    filter_upwards [hlogL.eventually_gt_atTop 0, hloglogL.eventually_gt_atTop 0] with L hl hll
    rw [log_div (hmlog L).ne' hl.ne']
    field_simp <;> ring
  have hxlog (L : ℕ) : log (x L) = log (C / 256) + log (m L) + log (log (m L)) := by
    change log ((C / 256) * (m L : ℝ) * log (m L)) = _
    rw [log_mul (mul_pos hκ (hmpos L)).ne' (hmlog L).ne',
      log_mul hκ.ne' (hmpos L).ne']
  have hx : Tendsto x atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hm
    filter_upwards [hlogm.eventually_ge_atTop (1 / (C / 256))] with L hl
    dsimp [x]
    have hb : 1 ≤ (C / 256) * log (m L) := by
      simpa only [mul_comm] using (div_le_iff₀ hκ).mp hl
    nlinarith [hmpos L]
  have hlogxlogm : Tendsto (fun L : ℕ => log (x L) / log (m L)) atTop (𝓝 1) := by
    have hq : Tendsto (fun L : ℕ => log (log (m L)) / log (m L)) atTop (𝓝 0) := (isLittleO_log_id_atTop.comp_tendsto hlogm).tendsto_div_nhds_zero
    have ht := (((tendsto_const_nhds (x := log (C / 256))).div_atTop hlogm).add hq).add_const 1
    simp only [zero_add] at ht
    apply ht.congr'
    filter_upwards [] with L
    rw [hxlog]
    field_simp [(hmlog L).ne']
    ring
  let missing : ℕ → Finset ℕ := fun L =>
    ((Ioc 0 (m L)).filter Nat.Prime).filter (fun p => p % 3 = 1 ∧ m L < 2 * p)
  let B : ℕ → ℝ := fun L => ∑ p ∈ missing L, -log (1 - (p : ℝ)⁻¹)
  let Z : ℕ → ℝ := fun L => ∑ p ∈ missing L, (p : ℝ)⁻¹
  let main : ℕ → ℝ := fun L =>
    (log (log (m L)) - log (log ((m L : ℝ) / 2))) / 2
  have hhalf : Tendsto (fun L : ℕ => (m L : ℝ) / 2) atTop atTop := by
    have hh := hm.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [div_eq_mul_inv, one_div, mul_comm, one_mul] using hh
  have hloga : Tendsto (fun L : ℕ => log ((m L : ℝ) / 2)) atTop atTop :=     tendsto_log_atTop.comp hhalf
  have hloghalf (L : ℕ) : log ((m L : ℝ) / 2) = log (m L) - log 2 :=     log_div (hmpos L).ne' (by norm_num)
  have hsets (L : ℕ) : missing L =
      (Ioc ⌊(m L : ℝ) / 2⌋₊ ⌊(m L : ℝ)⌋₊).filter
        (fun p => p.Prime ∧ p % 3 = 1) := by
    ext p
    simp only [missing, mem_filter, mem_Ioc, Nat.floor_natCast]
    constructor
    · rintro ⟨⟨⟨hp0, hpM⟩, hp⟩, hr, hgt⟩
      have hgtR : (m L : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hgt
      have hf : ⌊(m L : ℝ) / 2⌋₊ < p :=
        (Nat.floor_lt (by positivity)).mpr (by linarith)
      exact ⟨⟨hf, hpM⟩, hp, hr⟩
    · rintro ⟨⟨hf, hpM⟩, hp, hr⟩
      have hgtR := (Nat.floor_lt (by positivity : (0 : ℝ) ≤ (m L : ℝ) / 2)).mp hf
      have hgt : m L < 2 * p := by exact_mod_cast (show (m L : ℝ) < 2 * (p : ℝ) by linarith)
      exact ⟨⟨⟨hp.pos, hpM⟩, hp⟩, hr, hgt⟩
  have hratioHalf : Tendsto (fun L : ℕ => log (m L) / log ((m L : ℝ) / 2)) atTop (𝓝 1) := by
    have hh := (hloga.const_div_atTop (log 2)).add_const 1
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [hloga.eventually_gt_atTop 0] with L hl
    field_simp [hl.ne']
    rw [hloghalf]
    <;> ring
  have hq0 : Tendsto (fun L : ℕ => -(log 2 / log (m L))) atTop (𝓝 0) := by
    simpa only [neg_zero] using (hlogm.const_div_atTop (log 2)).neg
  have hqLeft : Tendsto (fun L : ℕ => -(log 2 / log (m L))) atTop (𝓝[<] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hq0, Eventually.of_forall (fun L => neg_neg_of_pos
      (div_pos (log_pos (by norm_num : (1 : ℝ) < 2)) (hmlog L)))⟩
  have htMain : Tendsto (fun L : ℕ => log (m L) * main L) atTop (𝓝 (log 2 / 2)) := by
    have hh := ((hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero_left.comp
      hqLeft).const_mul (log 2 / 2)
    simp only [inv_one, log_one, sub_zero, smul_eq_mul, mul_one] at hh
    apply hh.congr'
    filter_upwards [hloga.eventually_gt_atTop 0] with L hl
    have hlt := (hmlog L).ne'
    have hl2 : log (2 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
    have hminus : log (m L) - log 2 ≠ 0 := by rw [← hloghalf]; exact hl.ne'
    have hin : 1 + -(log 2 / log (m L)) = (log (m L) - log 2) / log (m L) := by
      field_simp
      ring
    dsimp only [Function.comp_def]
    rw [hin, log_div hminus hlt]
    dsimp only [main]
    rw [hloghalf]
    field_simp [hlt, hl2]
    <;> ring
  rcases isBigO_iff'.mp hTheta1 with ⟨K, hK, hbig⟩
  rcases eventually_atTop.mp hbig with ⟨Y, hY⟩
  have hdyadic : ∀ᶠ L : ℕ in atTop,
      |Z L - main L| ≤ 4 * K / log ((m L : ℝ) / 2) ^ 4 := by
    filter_upwards [hhalf.eventually_ge_atTop Y, hhalf.eventually_gt_atTop 1,
      hloga.eventually_ge_atTop 1] with L hLY hL1 hll
    have hr (u : ℝ) (hu : u ∈ Set.Icc ((m L : ℝ) / 2) (2 * ((m L : ℝ) / 2))) :
        |residueTheta 1 u - u / 2| ≤ K * u / log u ^ 3 := by
      have hu0 : 0 < u := by linarith [hu.1]
      have hlu : 0 < log u := log_pos (by linarith [hu.1])
      have hh := hY u (hLY.trans hu.1)
      change |residueTheta 1 u - u / 2| ≤ K * |u / log u ^ 3| at hh
      rw [abs_of_pos (by positivity : 0 < u / log u ^ 3)] at hh
      simpa only [mul_div_assoc] using hh
    have hh := dyadic ((m L : ℝ) / 2) K hL1 hll hK.le hr
    dsimp only [Z, main]
    rw [hsets]
    simpa only [show 2 * ((m L : ℝ) / 2) = (m L : ℝ) by ring] using hh
  have hupper : Tendsto (fun L : ℕ =>
      log (m L) * (4 * K / log ((m L : ℝ) / 2) ^ 4)) atTop (𝓝 0) := by
    have hh := (hratioHalf.mul ((hloga.const_div_atTop 1).pow 3)).const_mul (4 * K)
    simp only [zero_pow (by decide : 3 ≠ 0), mul_zero] at hh
    apply hh.congr'
    filter_upwards [hloga.eventually_gt_atTop 0] with L hl
    field_simp
    <;> ring
  have htError : Tendsto (fun L : ℕ => log (m L) * (Z L - main L)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hupper
    filter_upwards [hdyadic] with L hL
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hmlog L)]
    exact mul_le_mul_of_nonneg_left hL (hmlog L).le
  have htZ : Tendsto (fun L : ℕ => log (m L) * Z L) atTop (𝓝 (log 2 / 2)) := by
    have hh := htError.add htMain
    simp only [zero_add] at hh
    convert hh using 1
    ext L
    ring
  have hlogOverM : Tendsto (fun L : ℕ => log (m L) / (m L)) atTop (𝓝 0) := (isLittleO_log_id_atTop.comp_tendsto hm).tendsto_div_nhds_zero
  have htCorrection : Tendsto (fun L : ℕ => log (m L) * (B L - Z L)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := hlogOverM.const_mul 8
    simp only [mul_zero] at hh
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hh
    filter_upwards [] with L
    have hb := bandCorrection (m L) (by dsimp [m]; omega)
    change |B L - Z L| ≤ 8 / (m L : ℝ) at hb
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hmlog L)]
    calc
      _ ≤ log (m L) * (8 / (m L : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (hmlog L).le
      _ = 8 * (log (m L) / (m L : ℝ)) := by ring
  have htB : Tendsto (fun L : ℕ => log (m L) * B L) atTop (𝓝 (log 2 / 2)) := by
    have hh := htCorrection.add htZ
    simp only [zero_add] at hh
    convert hh using 1
    ext L
    ring
  let δ : ℕ → ℝ := fun L => ∏ p ∈ (A L).primeFactors,
    (1 - (p : ℝ)⁻¹ ^ ((A L).factorization p + 1))
  let J : ℕ → ℝ := fun L => ∏ p ∈ blockSet (m L) (x L), (1 - (p : ℝ)⁻¹ ^ 2)
  have hlogSqrt : Tendsto (fun L : ℕ => log L / sqrt L) atTop (𝓝 0) := by
    simpa only [sqrt_eq_rpow, Function.comp_def] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto hnat
        |>.tendsto_div_nhds_zero
  have htδ : Tendsto (fun L : ℕ => log (m L) * (δ L - 1)) atTop (𝓝 0) := by
    have hu := (hlogmL.mul hlogSqrt).const_mul 6
    simp only [mul_zero] at hu
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hu
    filter_upwards [eventually_ge_atTop (16 : ℕ), hlogL.eventually_gt_atTop 0] with L hL hl
    rcases arithmetic L (by omega) with
      ⟨hQ, hA, hcrit, hQ3, hv3, hlo, hup, hcore, hsig, hcoreN,
        h5040, hsize, hsat, hdef, hj, hhigh, hblock⟩
    have hh := hdef hL
    change |δ L - 1| ≤ 6 / sqrt (L : ℝ) at hh
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hmlog L)]
    calc
      _ ≤ log (m L) * (6 / sqrt (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (hmlog L).le
      _ = 6 * (log (m L) / log L * (log L / sqrt (L : ℝ))) := by
        field_simp [hl.ne']
        <;> ring
  have hδ : Tendsto δ atTop (𝓝 1) := by
    have hh := (htδ.div_atTop hlogm).add_const 1
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [] with L
    exact by field_simp [(hmlog L).ne'] <;> ring
  have htJ : Tendsto (fun L : ℕ => log (m L) * (J L - 1)) atTop (𝓝 0) := by
    have hu := hlogOverM.const_mul 4
    simp only [mul_zero] at hu
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hu
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with L hL
    rcases arithmetic L hL with
      ⟨hQ, hA, hcrit, hQ3, hv3, hlo, hup, hcore, hsig, hcoreN,
        h5040, hsize, hsat, hdef, hj, hhigh, hblock⟩
    have hh := hj (x L)
    change |J L - 1| ≤ 4 / ((3 * L + 3 : ℕ) : ℝ) at hh
    have hden : 4 / ((3 * L + 3 : ℕ) : ℝ) ≤ 4 / (m L : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (hmpos L)
      dsimp [m]
      push_cast
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hmlog L)]
    calc
      _ ≤ log (m L) * (4 / (m L : ℝ)) :=
        mul_le_mul_of_nonneg_left (hh.trans hden) (hmlog L).le
      _ = 4 * (log (m L) / (m L : ℝ)) := by ring
  have hJ : Tendsto J atTop (𝓝 1) := by
    have hh := (htJ.div_atTop hlogm).add_const 1
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [] with L
    field_simp [(hmlog L).ne']
    <;> ring
  have hB0 : Tendsto B atTop (𝓝 0) := by
    have hh := htB.div_atTop hlogm
    apply hh.congr'
    filter_upwards [] with L
    field_simp [(hmlog L).ne']
  have hBpos : ∀ᶠ L : ℕ in atTop, 0 < B L := by
    have hc : (0 : ℝ) < log 2 / 2 := by positivity
    filter_upwards [htB.eventually (lt_mem_nhds hc)] with L hL
    exact (mul_pos_iff.mp hL).resolve_right (by intro h; linarith [hmlog L])
      |>.2
  have hnegB : Tendsto (fun L : ℕ => -B L) atTop (𝓝[<] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [neg_zero] using hB0.neg,
      hBpos.mono (fun L hL => neg_neg_of_pos hL)⟩
  have htExp : Tendsto (fun L : ℕ => log (m L) * (exp (-B L) - 1)) atTop (𝓝 (-(log 2 / 2))) := by
    have hh := ((hasDerivAt_exp 0).tendsto_slope_zero_left.comp hnegB).mul htB.neg
    simp only [exp_zero, zero_add, smul_eq_mul, one_mul] at hh
    apply hh.congr'
    filter_upwards [hBpos] with L hL
    dsimp only [Function.comp_def]
    field_simp [hL.ne']
    <;> ring
  let F : ℕ → ℝ := fun L => exp (-B L) * δ L
  let G : ℕ → ℝ := fun L => F L * J L
  have hF : Tendsto F atTop (𝓝 1) := by
    have he : Tendsto (fun L : ℕ => exp (-B L)) atTop (𝓝 1) := by
      have hn : Tendsto (fun L : ℕ => -B L) atTop (𝓝 0) := by
        simpa only [neg_zero] using hB0.neg
      simpa only [exp_zero, Function.comp_def] using
        (Real.continuous_exp.tendsto 0).comp hn
    simpa only [F, one_mul] using he.mul hδ
  have hG : Tendsto G atTop (𝓝 1) := by
    simpa only [one_mul] using hF.mul hJ
  have htF : Tendsto (fun L : ℕ => log (m L) * (F L - 1)) atTop (𝓝 (-(log 2 / 2))) := by
    have hh := (htExp.mul hδ).add htδ
    simp only [mul_one, add_zero] at hh
    convert hh using 1
    ext L
    dsimp [F]
    ring
  have htG : Tendsto (fun L : ℕ => log (m L) * (G L - 1)) atTop (𝓝 (-(log 2 / 2))) := by
    have hh := (htF.mul hJ).add htJ
    simp only [mul_one, add_zero] at hh
    convert hh using 1
    ext L
    dsimp [G]
    ring
  have hsG : Tendsto (fun L : ℕ => log (x L) * (G L - 1)) atTop (𝓝 (-(log 2 / 2))) := by
    have hh := hlogxlogm.mul htG
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [] with L
    field_simp [(hmlog L).ne']
    <;> ring
  have hAWeight : Tendsto (fun L : ℕ => normalizedWeight (A L) - E * (log (m L) - log 2 / 2)) atTop (𝓝 0) := by
    have hh := ((hP.comp hm).mul hF).add ((htF.add_const (log 2 / 2)).const_mul E)
    simp only [zero_mul, neg_add_cancel, mul_zero, add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with L hL
    rcases arithmetic L (by omega) with
      ⟨hQ, hA, hcrit, hQ3, hv3, hlo, hup, hcore, hsig, hcoreN,
        h5040, hsize, hsat, hdef, hj, hhigh, hblock⟩
    have heq := hsat hL
    change normalizedWeight (A L) = primeProduct (m L) * exp (-B L) * δ L at heq
    rw [heq]
    dsimp [F, E]
    ring
  have hHWeight : Tendsto (fun L : ℕ => normalizedWeight (H L) - E * (log (x L) - log 2 / 2)) atTop (𝓝 0) := by
    have hh := ((hP.comp hx).mul hG).add ((hsG.add_const (log 2 / 2)).const_mul E)
    simp only [zero_mul, neg_add_cancel, mul_zero, add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (3 : ℕ),
      hlogm.eventually_ge_atTop (1 / (C / 256))] with L hL hl
    have hxm : (m L : ℝ) ≤ x L := by
      have hb : 1 ≤ (C / 256) * log (m L) := by
        simpa only [mul_comm] using (div_le_iff₀ hκ).mp hl
      dsimp [x]
      nlinarith [hmpos L]
    rcases arithmetic L (by omega) with
      ⟨hQ, hA, hcrit, hQ3, hv3, hlo, hup, hcore, hsig, hcoreN,
        h5040, hsize, hsat, hdef, hj, hhigh, hblock⟩
    have heq := (hhigh hL (x L) hxm).1
    change normalizedWeight (H L) = primeProduct (x L) * exp (-B L) * δ L * J L at heq
    rw [heq]
    dsimp [G, F, E]
    ring
  have thetaLimit (r : ℕ)
      (hθ : (fun y : ℝ => residueTheta r y - y / 2) =O[atTop]
        (fun y => y / log y ^ 3)) :
      Tendsto (fun y : ℝ => residueTheta r y / y) atTop (𝓝 (1 / 2 : ℝ)) := by
    have hg : (fun y : ℝ => y / log y ^ 3) =o[atTop] (fun y : ℝ => y) := by
      apply isLittleO_of_tendsto (fun y hy => by simp [hy])
      have hh := ((tendsto_log_atTop.const_div_atTop 1).pow 3)
      simp only [zero_pow (by decide : 3 ≠ 0)] at hh
      apply hh.congr'
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
      have hy0 : y ≠ 0 := by linarith
      field_simp [hy0]
      <;> ring
    have hh := (hθ.trans_isLittleO hg).tendsto_div_nhds_zero.add_const (1 / 2 : ℝ)
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    field_simp [hy.ne']
    <;> ring
  have hθ1 := thetaLimit 1 hTheta1
  have hθ2 := thetaLimit 2 hTheta2
  have hθm : Tendsto (fun L : ℕ =>
      (residueTheta 1 ((m L : ℝ) / 2) + residueTheta 2 (m L)) / (m L))
      atTop (𝓝 (3 / 4 : ℝ)) := by
    have hh := ((hθ1.comp hhalf).div_const 2).add (hθ2.comp hm)
    convert hh using 1 <;> norm_num <;>
      (try ext L) <;> (try dsimp only [Function.comp_def]) <;> field_simp <;> ring
  have hCoreErrorUpper : Tendsto (fun L : ℕ =>
      (log 3 + 2 * sqrt (m L) * log (m L)) / (m L))
      atTop (𝓝 0) := by
    have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto hm
      |>.tendsto_div_nhds_zero
    have hh := (hm.const_div_atTop (log 3)).add (hl.const_mul 2)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr'
    filter_upwards [] with L
    dsimp only [Function.comp_def]
    rw [← sqrt_eq_rpow]
    have hs := sqrt_pos.mpr (hmpos L)
    have hs2 := sq_sqrt (hmpos L).le
    field_simp [hs.ne', (hmpos L).ne']
    <;> linear_combination -2 * log (m L) * hs2
  have hCoreError : Tendsto (fun L : ℕ =>
      (log (A L) - (residueTheta 1 ((m L : ℝ) / 2) + residueTheta 2 (m L))) / (m L))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hCoreErrorUpper
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with L hL
    rcases arithmetic L (by omega) with
      ⟨hQ, hA, hcrit, hQ3, hv3, hlo, hup, hcore, hsig, hcoreN,
        h5040, hsize, hsat, hdef, hj, hhigh, hblock⟩
    have hh := hsize hL
    change |log (A L) -
      (residueTheta 1 ((m L : ℝ) / 2) + residueTheta 2 (m L))| ≤
        log 3 + 2 * sqrt (m L) * log (m L) at hh
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hmpos L)]
    exact div_le_div_of_nonneg_right hh (hmpos L).le
  have hCoreScale : Tendsto (fun L : ℕ => log (A L) / (m L)) atTop (𝓝 (3 / 4 : ℝ)) := by
    have hh := hCoreError.add hθm
    simp only [zero_add] at hh
    convert hh using 1
    ext L
    ring
  have hASize : Tendsto (fun L : ℕ => log (A L) / ((3 / 4 : ℝ) * (m L))) atTop (𝓝 1) := by
    have hh := hCoreScale.div_const (3 / 4 : ℝ)
    norm_num only [div_self] at hh
    apply hh.congr'
    filter_upwards [] with L
    field_simp
    <;> ring
  have thetaSplit (y : ℝ) (hy : 3 ≤ y) :
      Chebyshev.theta y = residueTheta 1 y + residueTheta 2 y + log 3 := by
    let P := (Ioc 0 ⌊y⌋₊).filter Nat.Prime
    have hthree : 3 ∈ P := by
      apply mem_filter.mpr
      exact ⟨mem_Ioc.mpr ⟨by decide, (Nat.le_floor_iff (by linarith)).mpr hy⟩,
        Nat.prime_three⟩
    have hθr (r : ℕ) : residueTheta r y =         ∑ p ∈ P, if p % 3 = r then log (p : ℝ) else 0 := by
      simp only [residueTheta, P, sum_filter]
      apply sum_congr rfl
      intro p _
      split_ifs <;> simp_all
    change (∑ p ∈ P, log (p : ℝ)) = _
    rw [hθr, hθr]
    have hthird : (∑ p ∈ P, if p = 3 then log (p : ℝ) else 0) = log 3 := by
      simp [hthree]
    rw [← hthird, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hpP
    have hp := (mem_filter.mp hpP).2
    by_cases hp3 : p = 3
    · simp [hp3]
    · have hr0 : p % 3 ≠ 0 := by
        intro hr
        exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
          (Nat.dvd_iff_mod_eq_zero.mpr hr)).symm
      have hrlt := Nat.mod_lt p (by decide : 0 < (3 : ℕ))
      rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with hr | hr <;> simp [hr, hp3]
  have hθtotal : Tendsto (fun y : ℝ => Chebyshev.theta y / y) atTop (𝓝 1) := by
    have hh := (hθ1.add hθ2).add (tendsto_id.const_div_atTop (log 3))
    norm_num only [add_zero, add_halves] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with y hy
    dsimp only [id]
    rw [thetaSplit y hy]
    ring
  have hMOverX : Tendsto (fun L : ℕ => (m L : ℝ) / x L) atTop (𝓝 0) := by
    have hh := hlogm.const_div_atTop (1 / (C / 256))
    apply hh.congr'
    filter_upwards [] with L
    dsimp only [x]
    field_simp [hκ.ne', (hmpos L).ne', (hmlog L).ne']
    <;> ring
  have hHSize : Tendsto (fun L : ℕ => log (H L) / x L) atTop (𝓝 1) := by
    have hh := ((hCoreScale.mul hMOverX).add (hθtotal.comp hx)).sub
      ((hθtotal.comp hm).mul hMOverX)
    simp only [mul_zero, zero_add, sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (3 : ℕ),
      hlogm.eventually_ge_atTop (1 / (C / 256))] with L hL hl
    have hxm : (m L : ℝ) ≤ x L := by
      have hb : 1 ≤ (C / 256) * log (m L) := by
        simpa only [mul_comm] using (div_le_iff₀ hκ).mp hl
      dsimp [x]
      nlinarith [hmpos L]
    rcases arithmetic L (by omega) with
      ⟨hQ, hA, hcrit, hQ3, hv3, hlo, hup, hcore, hsig, hcoreN,
        h5040, hsize, hsat, hdef, hj, hhigh, hblock⟩
    have hlogT := (hhigh hL (x L) hxm).2
    change log (T L) = Chebyshev.theta (x L) - Chebyshev.theta (m L) at hlogT
    have hT0 : (T L : ℝ) ≠ 0 := by
      have hTP : 0 < T L := (hblock (x L)).1
      exact_mod_cast hTP.ne'
    have hA0 : (A L : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
    have hlogH : log (H L) = log (A L) + log (T L) := by
      change log ((A L * T L : ℕ) : ℝ) = _
      rw [Nat.cast_mul, log_mul hA0 hT0]
    dsimp only [Function.comp_def]
    rw [hlogH, hlogT]
    field_simp [(hmpos L).ne', (hxpos L).ne']
    <;> ring
  have hscaleA : Tendsto (fun L : ℕ => log (A L) / (m L)) atTop (𝓝 (3 / 4 : ℝ)) := by
    have ht := hASize.mul_const (3 / 4 : ℝ)
    norm_num only [one_mul] at ht
    apply ht.congr'
    filter_upwards [] with L
    have hmp := hmpos L
    field_simp
  have hA9 : Tendsto (fun L : ℕ => log (A L) / ((9 / 4 : ℝ) * (L : ℝ)))       atTop (𝓝 1) := by
    have ht := hASize.mul (hmL.div_const 3)
    norm_num only [div_self, one_mul] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    field_simp [(hmpos L).ne', hL0] <;> ring
  have hLogA : Tendsto (fun L : ℕ => log (A L)) atTop atTop := by
    have hden := Filter.Tendsto.pos_mul_atTop (by norm_num : 0 < (3 / 4 : ℝ))
      tendsto_const_nhds hm
    have ht := hASize.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hden
    apply ht.congr'
    exact Eventually.of_forall (fun L => div_mul_cancel₀ _ (mul_pos (by norm_num) (hmpos L)).ne')
  have hLogH : Tendsto (fun L : ℕ => log (H L)) atTop atTop := by
    have ht := hHSize.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hx
    apply ht.congr'
    exact Eventually.of_forall (fun L => div_mul_cancel₀ _ (hxpos L).ne')
  have hsqrt : 0 < sqrt (2 : ℝ) := sqrt_pos.mpr (by norm_num)
  have hconstlog : log (3 / (2 * sqrt (2 : ℝ))) = log (3 / 4 : ℝ) + log 2 / 2 := by
    rw [log_div (by norm_num : (3 : ℝ) ≠ 0) (mul_ne_zero (by norm_num) hsqrt.ne'),
      log_mul (by norm_num : (2 : ℝ) ≠ 0) hsqrt.ne', log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    have hlog4 : log (4 : ℝ) = 2 * log 2 := by
      calc
        log (4 : ℝ) = log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * log 2 := log_pow (2 : ℝ) 2
    rw [hlog4]
    ring
  have hcA : 0 < E * log (3 / (2 * sqrt (2 : ℝ))) := by
    apply mul_pos hE (log_pos ?_)
    apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hsqrt)).mpr
    have hsq := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [sqrt_nonneg (2 : ℝ)]
  have hcH : 0 < (E / 2) * log 2 := mul_pos (by positivity) (log_pos (by norm_num))
  have hMarginA : Tendsto (fun L : ℕ => robinMargin (A L)) atTop       (𝓝 (E * log (3 / (2 * sqrt 2)))) := by
    have ht := (((hscaleA.log (by norm_num : (3 / 4 : ℝ) ≠ 0)).add_const (log 2 / 2)).const_mul E).sub hAWeight
    rw [sub_zero, ← hconstlog] at ht
    apply ht.congr'
    filter_upwards [hLogA.eventually_gt_atTop 0] with L hl
    rw [log_div hl.ne' (hmpos L).ne']
    dsimp [robinMargin, E]
    ring
  have hMarginH : Tendsto (fun L : ℕ => robinMargin (H L)) atTop (𝓝 ((E / 2) * log 2)) := by
    have ht := (((hHSize.log one_ne_zero).add_const (log 2 / 2)).const_mul E).sub hHWeight
    simp only [log_one, zero_add, sub_zero] at ht
    have hc : E * (log 2 / 2) = (E / 2) * log 2 := by ring
    rw [hc] at ht
    apply ht.congr'
    filter_upwards [hLogH.eventually_gt_atTop 0] with L hl
    rw [log_div hl.ne' (hxpos L).ne']
    dsimp [robinMargin, E]
    ring
  have hUANorm : Tendsto (fun L : ℕ => normalizedWeight (A L) / (E * log L))       atTop (𝓝 1) := by
    have hc := (tendsto_const_nhds (x := log (2 : ℝ) / 2)).div_atTop hlogL
    have hr := (hAWeight.div_const E).div_atTop hlogL
    have ht := (hlogmL.sub hc).add hr
    simp only [sub_zero, add_zero, zero_div] at ht
    apply ht.congr'
    filter_upwards [hlogL.eventually_gt_atTop 0] with L hl
    field_simp [hE.ne', hl.ne'] <;> ring
  have hLogDiff : Tendsto (fun L : ℕ => (log (x L) - log (m L)) / log (log L))       atTop (𝓝 1) := by
    have hc := (tendsto_const_nhds (x := log (C / 256))).div_atTop hloglogL
    have ht := hloglogmL.add hc
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [hloglogL.eventually_gt_atTop 0] with L hll
    rw [hxlog]
    field_simp
    ring
  have hAddRate : Tendsto (fun L : ℕ =>
      (normalizedWeight (H L) - normalizedWeight (A L)) / (E * log (log L)))
      atTop (𝓝 1) := by
    have hr := ((hHWeight.sub hAWeight).div_const E).div_atTop hloglogL
    have ht := hLogDiff.add hr
    simp only [sub_self, zero_div, add_zero] at ht
    apply ht.congr'
    filter_upwards [hloglogL.eventually_gt_atTop 0] with L hll
    field_simp [hE.ne', hll.ne'] <;> ring
  have hRelRate : Tendsto (fun L : ℕ =>
      (normalizedWeight (H L) / normalizedWeight (A L) - 1) * (log L / log (log L)))
      atTop (𝓝 1) := by
    have ht := hAddRate.mul (hUANorm.inv₀ one_ne_zero)
    simp only [inv_one, one_mul] at ht
    apply ht.congr'
    filter_upwards [hlogL.eventually_gt_atTop 0, hloglogL.eventually_gt_atTop 0,
      hUANorm.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with L hl hll hu
    have hu0 : normalizedWeight (A L) ≠ 0 := by
      intro hz
      simp [hz] at hu
    field_simp [hE.ne', hl.ne', hll.ne', hu0] <;> ring
  have hDiff : Tendsto (fun L : ℕ => normalizedWeight (H L) - normalizedWeight (A L))
      atTop atTop := by
    have hden : Tendsto (fun L : ℕ => E * log (log L)) atTop atTop :=
      Filter.Tendsto.pos_mul_atTop hE tendsto_const_nhds hloglogL
    have ht := hAddRate.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hden
    apply ht.congr'
    filter_upwards [hloglogL.eventually_gt_atTop 0] with L hll
    exact div_mul_cancel₀ _ (mul_pos hE hll).ne'
  have hxHeight : Tendsto (fun L : ℕ => x L / (C * (L : ℝ) * log L))
      atTop (𝓝 (3 / 256 : ℝ)) := by
    have ht := (hmL.mul hlogmL).div_const 256
    norm_num only [mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ), hlogL.eventually_gt_atTop 0] with L hL hl
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    dsimp [x]
    field_simp [hC.ne', hL0, hl.ne'] <;> ring
  have hHHeight : Tendsto (fun L : ℕ => log (H L) / (C * (L : ℝ) * log L))
      atTop (𝓝 (3 / 256 : ℝ)) := by
    have ht := hHSize.mul hxHeight
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [] with L
    field_simp [(hxpos L).ne']
  have hAHeight : Tendsto (fun L : ℕ => log (A L) / (C * (L : ℝ) * log L))
      atTop (𝓝 0) := by
    have hr := (tendsto_const_nhds (x := 1 / C)).div_atTop hlogL
    have ht := (hscaleA.mul hmL).mul hr
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ), hlogL.eventually_gt_atTop 0] with L hL hl
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    field_simp [(hmpos L).ne', hC.ne', hL0, hl.ne']
  constructor
  · intro L hL
    obtain ⟨hQp, hAp, hcrit, hQ3, hv3, hAlower, hAupper, hAcore, hsig, hcore,
      h5040, hSizeBound, hSaturation, hDefect, hSquarefree, hHighEuler, hblock⟩ := arithmetic L hL
    refine ⟨hQp, hAp, hQ3, hv3, hAlower, hAupper, hAcore, hsig, hcore, h5040, ?_⟩
    intro p hp
    simpa only [pow_one] using hcrit p 1 hp (by decide)
  ·
    refine ⟨hcA, hcH, hASize, hA9, hAWeight, hMarginA, hHSize, hHWeight,
      hMarginH, hRelRate, hAddRate, hDiff, ?_⟩
    filter_upwards [eventually_ge_atTop (16 : ℕ), hlogL.eventually_gt_atTop 0,
      hLogA.eventually_gt_atTop (log (5040 : ℝ)), hLogH.eventually_gt_atTop (log (5040 : ℝ)),
      hMarginA.eventually (lt_mem_nhds hcA), hMarginH.eventually (lt_mem_nhds hcH),
      hAHeight.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hHHeight.eventually (gt_mem_nhds (by norm_num : (3 / 256 : ℝ) < 1))]
      with L hL hl hAg hHg hAM hHM hAh hHh
    obtain ⟨hQp, hAp, hcrit, hQ3, hv3, hAlower, hAupper, hAcore, hsig, hcore, h5040, hSizeBound, hSaturation, hDefect, hSquarefree, hHighEuler, hblock⟩ :=
      arithmetic L (by omega)
    obtain ⟨hTp, hAT, hT3, hsigH, hHcore, hweights, hexponents⟩ := hblock (x L)
    have hHp : 0 < H L := Nat.mul_pos hAp hTp
    have hApR : 0 < (A L : ℝ) := by exact_mod_cast hAp
    have hHpR : 0 < (H L : ℝ) := by exact_mod_cast hHp
    have hAgt : 5040 < A L := by
      have h := (log_lt_log_iff (by norm_num : (0 : ℝ) < 5040) hApR).mp hAg
      exact_mod_cast h
    have hHgt : 5040 < H L := by
      have h := (log_lt_log_iff (by norm_num : (0 : ℝ) < 5040) hHpR).mp hHg
      exact_mod_cast h
    have hLp : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    have hbudget : 0 < C * (L : ℝ) * log L := mul_pos (mul_pos hC hLp) hl
    have hAheight : (A L : ℝ) ≤ exp (C * (L : ℝ) * log L) := by
      apply (log_le_iff_le_exp hApR).mp
      simpa only [one_mul] using le_of_lt ((div_lt_iff₀ hbudget).mp hAh)
    have hHheight : (H L : ℝ) ≤ exp (C * (L : ℝ) * log L) := by
      apply (log_le_iff_le_exp hHpR).mp
      simpa only [one_mul] using le_of_lt ((div_lt_iff₀ hbudget).mp hHh)
    have hAr : normalizedWeight (A L) < E * log (log (A L)) := by
      change 0 < E * log (log (A L)) - normalizedWeight (A L) at hAM
      linarith
    have hHr : normalizedWeight (H L) < E * log (log (H L)) := by
      change 0 < E * log (log (H L)) - normalizedWeight (H L) at hHM
      linarith
    refine ⟨hAp, hHp, hAgt, hHgt, h5040 hL, (h5040 hL).trans (dvd_mul_right _ _),
      hAr, hHr, hAM, hHM, hAheight, hHheight, hsigH, hAcore, hHcore, hAT, hQ3,
      hv3, hAlower, hAupper, ?_, hsig, hcore⟩
    intro p hp
    simpa only [pow_one] using hcrit p 1 hp (by decide)
end D5.S3.Arith.FibonacciAtomic.AffineLcmRobinMargins
#print axioms D5.S3.Arith.FibonacciAtomic.AffineLcmRobinMargins.result
#check @D5.S3.Arith.FibonacciAtomic.AffineLcmRobinMargins.result
